package lasagna

func PreparationTime(layers []string, time int) int {
	if time == 0 {
		time = 2
	}
	return len(layers) * time
}

func Quantities(layers []string) (noodles int, sauce float64) {
	for _, layer := range layers {
		switch layer {
		case "noodles":
			noodles += 50
		case "sauce":
			sauce += 0.2
		}
	}
	return
}

func AddSecretIngredient(friends, my []string) {
	my[len(my)-1] = friends[len(friends)-1]
}

func ScaleRecipe(quantities []float64, n int) []float64 {
	res := make([]float64, len(quantities))
	scale := float64(n) / 2
	for i, q := range quantities {
		res[i] = q * scale
	}
	return res
}
