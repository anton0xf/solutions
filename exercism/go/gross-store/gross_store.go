package gross

var units = map[string]int{
	"quarter_of_a_dozen": 3,
	"half_of_a_dozen":    6,
	"dozen":              12,
	"small_gross":        120,
	"gross":              144,
	"great_gross":        1728,
}

// Units stores the Gross Store unit measurements.
func Units() map[string]int {
	return units
}

// NewBill creates a new bill.
func NewBill() map[string]int {
	return map[string]int{}
}

// AddItem adds an item to customer bill.
func AddItem(bill, units map[string]int, item, unit string) bool {
	if n, in := units[unit]; in {
		bill[item] += n
		return true
	}
	return false
}

// RemoveItem removes an item from customer bill.
func RemoveItem(bill, units map[string]int, item, unit string) bool {
	nBill, inBill := bill[item]
	nUnit, isUnit := units[unit]
	if !inBill || !isUnit || nBill < nUnit {
		return false
	}
	if nBill == nUnit {
		delete(bill, item)
	} else {
		bill[item] -= nUnit
	}
	return true
}

// GetItem returns the quantity of an item that the customer has in his/her bill.
func GetItem(bill map[string]int, item string) (int, bool) {
	if n, in := bill[item]; in {
		return n, true
	} else {
		return 0, false
	}

}
