package blackjack

// ParseCard returns the integer value of a card following blackjack ruleset.
func ParseCard(card string) int {
	switch card {
	case "two":
		return 2
	case "three":
		return 3
	case "four":
		return 4
	case "five":
		return 5
	case "six":
		return 6
	case "seven":
		return 7
	case "eight":
		return 8
	case "nine":
		return 9
	case "ten":
		return 10
	case "jack":
		return 10
	case "queen":
		return 10
	case "king":
		return 10
	case "ace":
		return 11
	default:
		return 0
	}
}

// FirstTurn returns the decision for the first turn, given two cards of the
// player and one card of the dealer.
func FirstTurn(card1, card2, dealerCard string) string {
	your := ParseCard(card1) + ParseCard(card2)
	dealer := ParseCard(dealerCard)
	switch {
	case your == 22:
		return "P"
	case your == 21:
		if dealer >= 10 {
			return "S"
		} else {
			return "W"
		}
	case 17 <= your && your <= 20:
		return "S"
	case 12 <= your && your <= 16:
		if dealer < 7 {
			return "S"
		} else {
			return "H"
		}
	default:
		return "H"
	}
}
