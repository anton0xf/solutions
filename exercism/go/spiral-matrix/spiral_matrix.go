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

func SpiralMatrix(size int) [][]int {
	var m = make([][]int, size)
	for i := range m {
		m[i] = make([]int, size)
	}
	// initial position
	p := vec{0, -1}
	// initial direction
	dir := vec{0, 1}
	// count of steps along direction
	steps := size
	step := 0
	// number of rotations before steps decreasing
	const rots = 2
	rot := 1 // decrease steps after first rotation
	for n := 1; n <= size * size; n++ {
		if step == steps {
			step = 0
			dir = dir.rotate()
			rot++
			if rot == rots {
				rot = 0
				steps--
			}
		}
		step++
		p = p.plus(dir)
		m[p.i][p.j] = n
	}
	
	return m
}
