package spiralmatrix

// vec is a vector in the matrix index coordinates
type vec struct {
	i int // zero-based row index
	j int // zero-based column index
}

func (v vec) plus(u vec) vec {
	return vec{v.i + u.i, v.j + u.j}
}

// rotate returns the input vector rotated clockwise by 90-degrees
func (v vec) rotate() vec {
	return vec{v.j, -v.i}
}

func (v vec) in(bounds vec) bool {
	return 0 <= v.i && v.i < bounds.i &&
		0 <= v.j && v.j < bounds.j
}

func SpiralMatrix(size int) [][]int {
	var m = make([][]int, size)
	for i := range m {
		m[i] = make([]int, size)
	}
	p := vec{0, -1} // initial position
	dir := vec{0, 1} // initial direction
	bounds := vec{size, size}
	for n := 1; n <= size * size; n++ {
		pn := p.plus(dir) // next positions
		if !pn.in(bounds) || m[pn.i][pn.j] != 0 {
			dir = dir.rotate()
			pn = p.plus(dir)
		}
		p = pn
		m[p.i][p.j] = n
	}
	
	return m
}
