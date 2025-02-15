package birdwatcher

// TotalBirdCount return the total bird count by summing
// the individual day's counts.
func TotalBirdCount(birdsPerDay []int) int {
	sum := 0
	for _, n := range birdsPerDay {
		sum += n
	}
	return sum
}

const daysInWeek = 7

// BirdsInWeek returns the total bird count by summing
// only the items belonging to the given week.
func BirdsInWeek(birdsPerDay []int, week int) int {
	firstDay := daysInWeek * (week - 1)
	return TotalBirdCount(birdsPerDay[firstDay : firstDay+daysInWeek])
}

// FixBirdCountLog returns the bird counts after correcting
// the bird counts for alternate days.
func FixBirdCountLog(birdsPerDay []int) []int {
	for i, n := range birdsPerDay {
		if i%2 == 0 {
			birdsPerDay[i] = n + 1
		}
	}
	return birdsPerDay
}
