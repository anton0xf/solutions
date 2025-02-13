package chance

import "math/rand"

// RollADie returns a random int d with 1 <= d <= 20.
func RollADie() int {
	return rand.Intn(20) + 1
}

// GenerateWandEnergy returns a random float64 f with 0.0 <= f < 12.0.
func GenerateWandEnergy() float64 {
	return rand.Float64() * 12
}

var animals = []string{
	"ant",
	"beaver",
	"cat",
	"dog",
	"elephant",
	"fox",
	"giraffe",
	"hedgehog",
}

// ShuffleAnimals returns a slice with all eight animal strings in random order.
func ShuffleAnimals() []string {
	res := make([]string, len(animals))
	copy(res, animals)
	rand.Shuffle(len(res), func(i int, j int) {
		res[i], res[j] = res[j], res[i]
	})
	return res
}
