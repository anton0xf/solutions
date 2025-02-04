// Package weather forecast the current weather condition of various cities in Goblinocus.
package weather

// CurrentCondition represents current weather condition.
var CurrentCondition string

// CurrentLocation represents current city.
var CurrentLocation string

// Forecast returns a string representation of weather forecast.
func Forecast(city, condition string) string {
	CurrentLocation, CurrentCondition = city, condition
	return CurrentLocation + " - current weather condition: " + CurrentCondition
}
