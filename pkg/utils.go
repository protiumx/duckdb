package pkg

func assert(condition bool) {
	if !condition {
		panic("failed assertion")
	}
}
