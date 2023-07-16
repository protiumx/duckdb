package pkg

import (
	"bytes"
	"encoding/binary"
)

// node format:
// | type | nkeys |  pointers  |   offsets  | key-values
// |  2B  |   2B  | nkeys * 8B | nkeys * 2B | ...

// key-value format:
// | klen | vlen | key | val |
// |  2B  |  2B  | ... | ... |

const (
	BNODE_NODE = iota + 1 // internal nodes
	BNODE_LEAF

	HEADER_SIZE        = 4
	BTREE_PAGE_SIZE    = 4096
	BTREE_MAX_KEY_SIZE = 1000
	BTREE_MAX_VAL_SIZE = 3000
)

type BNode struct {
	data []byte
}

type BTree struct {
	// pointer to memory page
	root uint64

	get func(uint64) BNode
	new func(BNode) uint64
	del func(uint64)
}

func init() {
	node_max_size := HEADER_SIZE + 8 + 2 + 4 + BTREE_MAX_KEY_SIZE + BTREE_MAX_VAL_SIZE
	assert(node_max_size <= BTREE_PAGE_SIZE)
}

func (n BNode) btype() uint16 {
	return binary.LittleEndian.Uint16(n.data)
}

func (n BNode) nkeys() uint16 {
	return binary.LittleEndian.Uint16(n.data[2:4])
}

func (n BNode) set_header(btype, nkeys uint16) {
	binary.LittleEndian.PutUint16(n.data[0:2], btype)
	binary.LittleEndian.PutUint16(n.data[2:4], nkeys)
}

func (n BNode) get_ptr(idx uint16) uint64 {
	assert(idx < n.nkeys())
	pos := HEADER_SIZE + 8*idx
	return binary.LittleEndian.Uint64(n.data[pos:])
}

func (n BNode) set_ptr(idx uint16, val uint64) {
	assert(idx < n.nkeys())
	pos := HEADER_SIZE + 8*idx
	binary.LittleEndian.PutUint64(n.data[pos:], val)
}

func offset_pos(node BNode, idx uint16) uint16 {
	assert(1 <= idx && idx <= node.nkeys())
	return HEADER_SIZE + 8*node.nkeys() + 2*(idx-1)
}

func (n BNode) get_offset(idx uint16) uint16 {
	// first node always is offset 0
	if idx == 0 {
		return 0
	}

	return binary.LittleEndian.Uint16(n.data[offset_pos(n, idx):])
}

func (n BNode) set_offset(idx, offset uint16) {
	binary.LittleEndian.PutUint16(n.data[offset_pos(n, idx):], offset)
}

func (n BNode) kv_pos(idx uint16) uint16 {
	assert(idx <= n.nkeys())
	return HEADER_SIZE + 8*n.nkeys() + 2*n.nkeys() + n.get_offset(idx)
}

func (n BNode) get_key(idx uint16) []byte {
	assert(idx < n.nkeys())
	pos := n.kv_pos(idx)
	klen := binary.LittleEndian.Uint16(n.data[pos:])
	return n.data[pos+4:][:klen]
}

func (n BNode) get_val(idx uint16) []byte {
	assert(idx < n.nkeys())
	pos := n.kv_pos(idx)
	klen := binary.LittleEndian.Uint16(n.data[pos+0:])
	vlen := binary.LittleEndian.Uint16(n.data[pos+2:])
	return n.data[pos+4+klen:][:vlen]
}

// size of a node
func (n BNode) nbytes() uint16 {
	return n.kv_pos(n.nkeys())
}

// return first leaf whose range intersects the key
func node_lookup_LE(node BNode, key []byte) uint16 {
	nkeys := node.nkeys()
	found := uint16(0)
	// first key is a copy from the parent node
	for i := uint16(1); i < nkeys; i++ {
		cmp := bytes.Compare(node.get_key(i), key)
		if cmp <= 0 {
			found = i
		}

		if cmp >= 0 {
			break
		}
	}

	return found
}

func leaf_insert(new, old BNode, idx uint16, key, val []byte) {
	new.set_header(BNODE_LEAF, old.nkeys()+1)
	node_append_range(new, old, 0, 0, idx)
	node_append_kv(new, idx, 0, key, val)
	node_append_range(new, old, idx+1, idx, old.nkeys()-idx)
}

func leaf_update(new, old BNode, idx uint16, key, val []byte) {
	new.set_header(BNODE_LEAF, old.nkeys())
	node_append_range(new, old, 0, 0, idx)
	node_append_kv(new, idx, 0, key, val)
	node_append_range(new, old, idx+1, idx+1, old.nkeys()-(idx+1))
}

func node_append_range(new, old BNode, dst, src, n uint16) {
	assert(src+n <= old.nkeys())
	assert(dst+n <= new.nkeys())

	if n == 0 {
		return
	}

	// copy pointers
	for i := uint16(0); i < n; i++ {
		new.set_ptr(dst+i, old.get_ptr(src+i))
	}

	// offsets
	dest_begin := new.get_offset(dst)
	src_begin := old.get_offset(src)
	for i := uint16(1); i <= n; i++ {
		offset := dest_begin + old.get_offset(src+i) - src_begin
		new.set_offset(dst+i, offset)
	}

	// copy KVs
	kv_begin := old.kv_pos(src)
	kv_end := old.kv_pos(src + n)
	copy(new.data[new.kv_pos(dst):], old.data[kv_begin:kv_end])
}

func node_append_kv(new BNode, idx uint16, ptr uint64, key, val []byte) {
	new.set_ptr(idx, ptr)

	pos := new.kv_pos(idx)
	binary.LittleEndian.PutUint16(new.data[pos+0:], uint16(len(key)))
	binary.LittleEndian.PutUint16(new.data[pos+2:], uint16(len(val)))

	copy(new.data[pos+4:], key)
	copy(new.data[pos+4+uint16(len(key)):], val)

	// set offset of the new key
	new.set_offset(idx+1, new.get_offset(idx)+4+uint16(len(key)+len(val)))
}

// split a bigger-than-allowed node into two.
// the second node always fits on a page.
func node_split2(left, right, old BNode) {
	assert(old.nkeys() >= 2)

	// the initial guess
	nleft := old.nkeys() / 2

	// try to fit the left half
	left_bytes := func() uint16 {
		return HEADER_SIZE + 8*nleft + 2*nleft + old.get_offset(nleft)
	}

	for left_bytes() > BTREE_PAGE_SIZE {
		nleft--
	}

	assert(nleft >= 1)

	// try to fit the right half
	right_bytes := func() uint16 {
		return old.nbytes() - left_bytes() + HEADER_SIZE
	}

	for right_bytes() > BTREE_PAGE_SIZE {
		nleft++
	}

	assert(nleft < old.nkeys())

	nright := old.nkeys() - nleft
	left.set_header(old.btype(), nleft)
	right.set_header(old.btype(), nright)

	node_append_range(left, old, 0, 0, nleft)
	node_append_range(right, old, 0, nleft, nright)
	// the left half may be still too big
	assert(right.nbytes() <= BTREE_PAGE_SIZE)
}

func node_split3(old BNode) (uint16, [3]BNode) {
	if old.nbytes() <= BTREE_PAGE_SIZE {
		old.data = old.data[:BTREE_PAGE_SIZE]
		return 1, [3]BNode{old}
	}

	left := BNode{make([]byte, 2*BTREE_PAGE_SIZE)} // might split later
	right := BNode{make([]byte, BTREE_PAGE_SIZE)}

	node_split2(left, right, old)
	if left.nbytes() <= BTREE_PAGE_SIZE {
		left.data = left.data[:BTREE_PAGE_SIZE]
		return 2, [3]BNode{left, right}
	}

	// left node is still too large
	left_left := BNode{make([]byte, BTREE_PAGE_SIZE)}
	middle := BNode{make([]byte, BTREE_PAGE_SIZE)}
	node_split2(left_left, middle, left)

	assert(left_left.nbytes() <= BTREE_PAGE_SIZE)

	return 3, [3]BNode{left_left, middle, right}
}

func node_replace_1(new, old BNode, idx uint16, ptr uint64) {
	copy(new.data, old.data[:old.nbytes()])
	new.set_ptr(idx, ptr) // only the pointer changed
}

// replace 2 adjacent links with 1
func node_replace_2(new, old BNode, idx uint16, ptr uint64, key []byte) {
	new.set_header(BNODE_NODE, old.nkeys()-1)
	node_append_range(new, old, 0, 0, idx)
	node_append_kv(new, idx, ptr, key, nil)
	node_append_range(new, old, idx+1, idx+2, old.nkeys()-(idx+2))
}

// replace N links
func node_replace_N(tree *BTree, new, old BNode, idx uint16, kids ...BNode) {
	inc := uint16(len(kids))

	if inc == 1 && bytes.Equal(kids[0].get_key(0), old.get_key(idx)) {
		// only replace 1 pointer
		node_replace_1(new, old, idx, tree.new(kids[0]))
		return
	}

	new.set_header(BNODE_NODE, old.nkeys()+inc-1)
	node_append_range(new, old, 0, 0, idx)
	for i, node := range kids {
		node_append_kv(new, idx+uint16(i), tree.new(node), node.get_key(0), nil)
	}

	node_append_range(new, old, idx+inc, idx+1, old.nkeys()-(idx+1))
}

// the result might be split into 2 node.
// the caller is responsible for deallocating the input node
// and splitting and allocating result nodes
func tree_insert(tree *BTree, node BNode, key, val []byte) BNode {
	new := BNode{data: make([]byte, 2*BTREE_PAGE_SIZE)}

	idx := node_lookup_LE(node, key)
	switch node.btype() {
	case BNODE_LEAF:
		// leaf
		if bytes.Equal(key, node.get_key(idx)) {
			// update
			leaf_update(new, node, idx, key, val)
		} else {
			// insert after idx
			leaf_insert(new, node, idx+1, key, val)
		}

	case BNODE_NODE:
		// internal node
		node_insert(tree, new, node, idx, key, val)

	default:
		panic("unknown node")
	}

	return new
}

func node_insert(tree *BTree, new, node BNode, idx uint16, key, val []byte) {
	// deallocate the child node
	kptr := node.get_ptr(idx)
	knode := tree.get(kptr)
	tree.del(kptr)

	// recursive insertion
	knode = tree_insert(tree, knode, key, val)
	nsplit, splited := node_split3(knode)
	node_replace_N(tree, new, node, idx, splited[:nsplit]...)
}

func leaf_delete(new, old BNode, idx uint16) {
	new.set_header(BNODE_LEAF, old.nkeys()-1)
	node_append_range(new, old, 0, 0, idx)
	node_append_range(new, old, idx, idx+1, old.nkeys()-(idx+1))
}

func tree_delete(tree *BTree, node BNode, key []byte) BNode {
	idx := node_lookup_LE(node, key)
	switch node.btype() {
	case BNODE_LEAF:
		if !bytes.Equal(key, node.get_key(idx)) {
			return BNode{} // not found
		}

		new := BNode{make([]byte, BTREE_PAGE_SIZE)}
		leaf_delete(new, node, idx)
		return new

	case BNODE_NODE:
		return node_delete(tree, node, idx, key)

	default:
		panic("unknown node type")
	}
}

func node_delete(tree *BTree, node BNode, idx uint16, key []byte) BNode {
	kptr := node.get_ptr(idx)
	updated := tree_delete(tree, tree.get(kptr), key)
	if len(updated.data) == 0 {
		return BNode{} // not found
	}

	tree.del(kptr)

	new := BNode{make([]byte, BTREE_PAGE_SIZE)}
	merge_dir, sibling := should_merge(tree, node, idx, updated)

	switch {
	case merge_dir < 0: // left
		merged := BNode{make([]byte, BTREE_PAGE_SIZE)}
		node_merge(merged, sibling, updated)
		tree.del(node.get_ptr(idx - 1))
		node_replace_2(new, node, idx-1, tree.new(merged), merged.get_key(0))

	case merge_dir > 0: // right
		merged := BNode{make([]byte, BTREE_PAGE_SIZE)}
		node_merge(merged, updated, sibling)
		tree.del(node.get_ptr(idx + 1))
		node_replace_2(new, node, idx, tree.new(merged), merged.get_key(0))

	case merge_dir == 0:
		assert(updated.nkeys() > 0)
		node_replace_N(tree, new, node, idx, updated)
	}

	return new
}

func node_merge(new, left, right BNode) {
	new.set_header(left.btype(), left.nkeys()+right.nkeys())
	node_append_range(new, left, 0, 0, left.nkeys())
	node_append_range(new, right, left.nkeys(), 0, right.nkeys())
	assert(new.nbytes() <= BTREE_PAGE_SIZE)
}

func should_merge(tree *BTree, node BNode, idx uint16, updated BNode) (int, BNode) {
	if updated.nkeys() > BTREE_PAGE_SIZE/4 {
		return 0, BNode{}
	}

	if idx > 0 {
		sibling := tree.get(node.get_ptr(idx - 1))
		merged := sibling.nbytes() + updated.nbytes() - HEADER_SIZE
		if merged <= BTREE_PAGE_SIZE {
			return -1, sibling
		}
	}

	if idx+1 < node.nkeys() {
		sibling := tree.get(node.get_ptr(idx + 1))
		merged := sibling.nbytes() + updated.nbytes() - HEADER_SIZE
		if merged <= BTREE_PAGE_SIZE {
			return +1, sibling
		}
	}

	return 0, BNode{}
}

func (t *BTree) Delete(key []byte) bool {
	assert(len(key) != 0)
	assert(len(key) <= BTREE_MAX_KEY_SIZE)

	if t.root == 0 {
		return false
	}

	updated := tree_delete(t, t.get(t.root), key)
	if len(updated.data) == 0 {
		// not found
		return false
	}

	t.del(t.root)
	if updated.btype() == BNODE_NODE && updated.nkeys() == 1 {
		t.root = updated.get_ptr(0) // remove level
	} else {
		t.root = t.new(updated)
	}

	return true
}

func (t *BTree) Insert(key, val []byte) {
	assert(len(key) != 0)
	assert(len(key) <= BTREE_MAX_KEY_SIZE)
	assert(len(val) <= BTREE_MAX_VAL_SIZE)

	if t.root == 0 {
		root := BNode{make([]byte, BTREE_PAGE_SIZE)}
		root.set_header(BNODE_LEAF, 2)
		// add dummy key thus look up can always find a containing node
		node_append_kv(root, 0, 0, nil, nil)
		node_append_kv(root, 1, 0, key, val)

		t.root = t.new(root)
		return
	}

	node := t.get(t.root)
	t.del(t.root)

	node = tree_insert(t, node, key, val)
	nsplit, splitted := node_split3(node)

	if nsplit > 1 {
		// root was split, add new level
		root := BNode{make([]byte, BTREE_PAGE_SIZE)}
		root.set_header(BNODE_NODE, nsplit)
		for i, knode := range splitted[:nsplit] {
			ptr, key := t.new(knode), knode.get_key(0)
			node_append_kv(root, uint16(i), ptr, key, nil)
		}
		t.root = t.new(root)
	} else {
		t.root = t.new(splitted[0])
	}
}
