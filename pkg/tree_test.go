package pkg

import (
	"fmt"
	"sort"
	"testing"
	"unsafe"

	is "github.com/stretchr/testify/require"
)

type test_container struct {
	tree  BTree
	ref   map[string]string
	pages map[uint64]BNode
}

func new_test_container() *test_container {
	pages := map[uint64]BNode{}

	return &test_container{
		tree: BTree{
			get: func(ptr uint64) BNode {
				node, ok := pages[ptr]
				assert(ok)
				return node
			},

			new: func(node BNode) uint64 {
				assert(node.nbytes() <= BTREE_PAGE_SIZE)
				key := uint64(uintptr(unsafe.Pointer(&node.data[0])))
				assert(pages[key].data == nil)
				pages[key] = node

				return key
			},

			del: func(ptr uint64) {
				_, ok := pages[ptr]
				assert(ok)
				delete(pages, ptr)
			},
		},
		ref:   map[string]string{},
		pages: pages,
	}
}

func (c *test_container) add(key, val string) {
	c.tree.Insert([]byte(key), []byte(val))
	c.ref[key] = val
}

func (c *test_container) del(key string) bool {
	delete(c.ref, key)
	return c.tree.Delete([]byte(key))
}

func (c *test_container) dump() ([]string, []string) {
	keys := []string{}
	vals := []string{}

	var node_dump func(uint64)
	node_dump = func(ptr uint64) {
		node := c.tree.get(ptr)
		nkeys := node.nkeys()
		if node.btype() == BNODE_LEAF {
			for i := uint16(0); i < nkeys; i++ {
				keys = append(keys, string(node.get_key(i)))
				vals = append(vals, string(node.get_val(i)))
			}
		} else {
			for i := uint16(0); i < nkeys; i++ {
				ptr := node.get_ptr(i)
				node_dump(ptr)
			}
		}
	}

	node_dump(c.tree.root)
	assert(keys[0] == "")
	assert(vals[0] == "")
	return keys[1:], vals[1:]
}

type sort_if struct {
	len  int
	less func(i, j int) bool
	swap func(i, j int)
}

func (self sort_if) Len() int {
	return self.len
}
func (self sort_if) Less(i, j int) bool {
	return self.less(i, j)
}
func (self sort_if) Swap(i, j int) {
	self.swap(i, j)
}

func (c *test_container) verify(t *testing.T) {
	keys, vals := c.dump()

	rkeys, rvals := []string{}, []string{}
	for k, v := range c.ref {
		rkeys = append(rkeys, k)
		rvals = append(rvals, v)
	}

	is.Equal(t, len(rkeys), len(keys))
	sort.Stable(sort_if{
		len:  len(rkeys),
		less: func(i, j int) bool { return rkeys[i] < rkeys[j] },
		swap: func(i, j int) {
			k, v := rkeys[i], rvals[i]
			rkeys[i], rvals[i] = rkeys[j], rvals[j]
			rkeys[j], rvals[j] = k, v
		},
	})

	is.Equal(t, rkeys, keys)
	is.Equal(t, rvals, vals)

	var node_verify func(BNode)
	node_verify = func(node BNode) {
		nkeys := node.nkeys()
		assert(nkeys >= 1)
		if node.btype() == BNODE_LEAF {
			return
		}
		for i := uint16(0); i < nkeys; i++ {
			key := node.get_key(i)
			kid := c.tree.get(node.get_ptr(i))
			is.Equal(t, key, kid.get_key(0))
			node_verify(kid)
		}
	}

	node_verify(c.tree.get(c.tree.root))
}

// avalanche function
// https://en.wikipedia.org/wiki/MurmurHash
func fmix32(h uint32) uint32 {
	h ^= h >> 16
	h *= 0x85ebca6b
	h ^= h >> 13
	h *= 0xc2b2ae35
	h ^= h >> 16
	return h
}

func TestBasic(t *testing.T) {
	c := new_test_container()
	c.add("k", "v")
	c.verify(t)

	// insert
	for i := 0; i < 250000; i++ {
		key := fmt.Sprintf("key%d", fmix32(uint32(i)))
		val := fmt.Sprintf("vvv%d", fmix32(uint32(-i)))
		c.add(key, val)
		if i < 2000 {
			c.verify(t)
		}
	}

	c.verify(t)

	// del
	for i := 2000; i < 250000; i++ {
		key := fmt.Sprintf("key%d", fmix32(uint32(i)))
		is.True(t, c.del(key))
	}
	c.verify(t)

	// overwrite
	for i := 0; i < 2000; i++ {
		key := fmt.Sprintf("key%d", fmix32(uint32(i)))
		val := fmt.Sprintf("vvv%d", fmix32(uint32(+i)))
		c.add(key, val)
		c.verify(t)
	}

	is.False(t, c.del("kk"))

	for i := 0; i < 2000; i++ {
		key := fmt.Sprintf("key%d", fmix32(uint32(i)))
		is.True(t, c.del(key))
		c.verify(t)
	}

	c.add("k", "v2")
	c.verify(t)
	c.del("k")
	c.verify(t)

	// the dummy empty key
	is.Equal(t, 1, len(c.pages))
	is.Equal(t, uint16(1), c.tree.get(c.tree.root).nkeys())
}
