package main

import (
	"basic/rvp"
	"basic/rvq"
	"basic/rvr"
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

func checkR(step string, err error, m *rvr.Monitor, expectedSuccess bool) {
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

func testDisj() {

	parties := map[string]map[string]bool{"P": {"p1": true}}
	m := rvp.NewMonitor(parties)

	err := m.Step(rvp.Global{B: 1}, rvp.PChangeB1)
	checkP("b1 state", err, m, true)

	err = m.StepA(rvp.PChangeB2)
	checkP("b2", err, m, true)

	err = m.StepA(rvp.PChangeB3)
	checkP("b3", err, m, false)

	m = rvp.NewMonitor(parties)

	err = m.Step(rvp.Global{B: 1}, rvp.PChangeB1)
	checkP("b1 state", err, m, true)

	err = m.Step(rvp.Global{B: 99}, rvp.PChangeB3)
	checkP("b3 state", err, m, false)

	m.PrintLog()
}

func testPreamble() {

	parties := map[string]map[string]bool{"Q": {"q1": true}}
	m := rvq.NewMonitor(parties)

	err := m.StepA(rvq.QChangeC3)
	checkQ("wrong order", err, m, false)

	err = m.Step(rvq.Global{B: 1, C: 1}, rvq.QChangeB1)
	checkQ("first step", err, m, true)

	// there is no way for this to be taken regardless of state because of the logical precondition
	err = m.Step(rvq.Global{B: 1, C: 3}, rvq.QChangeC4)
	checkQ("disjunct 1", err, m, false)

	err = m.Step(rvq.Global{B: 2, C: 3}, rvq.QChangeC4)
	checkQ("disjunct 2", err, m, false)

	// this one only works if in the right state
	err = m.Step(rvq.Global{B: 2, C: 2}, rvq.QChangeC3)
	checkQ("disjunct 3", err, m, false)

	err = m.Step(rvq.Global{B: 1, C: 2}, rvq.QChangeC3)
	checkQ("disjunct 4", err, m, true)

	m.PrintLog()
}

func testJoin() {

	parties := map[string]map[string]bool{"R": {"r1": true}, "S": {"s1": true, "s2": true}}
	m := rvr.NewMonitor(parties)

	err := m.Step(rvr.Global{A: 1}, rvr.RChangeA1)
	checkR("start", err, m, true)

	err = m.StepA(rvr.RChangeA1)
	checkR("cannot move on before both parties 1", err, m, false)

	fmt.Println("!!")
	fmt.Println(map[string]rvr.Any{"to": "s1", "type": "m"})

	err = m.Step(rvr.Global{A: 1, History1: map[string]rvr.Any{"to": "s1", "type": "m"}}, rvr.RSendM2, "s1")
	checkR("first party", err, m, true)

	err = m.StepA(rvr.RChangeA1)
	checkR("cannot move on before both parties 2", err, m, false)

	err = m.Step(rvr.Global{A: 1, History1: map[string]rvr.Any{"to": "s2", "type": "m"}}, rvr.RSendM2, "s2")
	checkR("second party", err, m, true)

	err = m.Step(rvr.Global{A: 2, History1: map[string]rvr.Any{"to": "s2", "type": "m"}}, rvr.RChangeA3)
	checkR("final state change", err, m, true)

	m.PrintLog()
}
func main() {
	testDisj()
	fmt.Println("---")
	testPreamble()
	fmt.Println("---")
	testJoin()
}
