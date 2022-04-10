package main

import (
	"basic/rvp"
	"basic/rvq"

	// "basic/rvr"
	"fmt"
)

func checkP(step string, err error, m *rvp.Monitor, expectedSuccess bool) {
	println("check", step)
	if err != nil {
		expected := ""
		if !expectedSuccess {
			expected = " (expected)"
		}
		fmt.Printf("  error = %v%s\n", err, expected)
		if expectedSuccess {
			panic("expected success but failed")
		}
	} else {
		fmt.Printf("  pc = %v\n", m.PC)
		if !expectedSuccess {
			panic("expected failure but succeeded")
		}
	}
}

func checkQ(step string, err error, m *rvq.Monitor, expectedSuccess bool) {
	println("check", step)
	if err != nil {
		expected := ""
		if !expectedSuccess {
			expected = " (expected)"
		}
		fmt.Printf("  error = %v%s\n", err, expected)
		if expectedSuccess {
			panic("expected success but failed")
		}
	} else {
		fmt.Printf("  pc = %v\n", m.PC)
		if !expectedSuccess {
			panic("expected failure but succeeded")
		}
	}
}

func tryP() {

	// disjunction

	parties := map[string]map[string]bool{"P": {"p1": true}}
	m := rvp.NewMonitor(parties)

	err := m.Step(rvp.Global{B: 2}, rvp.PChangeB1)
	checkP("b1", err, m, true)

	err = m.StepA(rvp.PChangeB2)
	checkP("b2", err, m, false)

	m = rvp.NewMonitor(parties)

	err = m.Step(rvp.Global{B: 3}, rvp.PChangeB2)
	checkP("b2", err, m, true)

	err = m.StepA(rvp.PChangeB1)
	checkP("b1", err, m, false)

	m.PrintLog()
}

func tryQ() {

	// preamble

	parties := map[string]map[string]bool{"Q": {"q1": true}}
	m := rvq.NewMonitor(parties)

	err := m.Step(rvq.Global{B: 2}, rvq.QChangeC3)
	checkQ("wrong order", err, m, false)

	err = m.Step(rvq.Global{C: 1}, rvq.QChangeB1)
	checkQ("b1", err, m, true)

	m.PrintLog()
}

func main() {
	// tryP()
	fmt.Println("---")
	tryQ()
}
