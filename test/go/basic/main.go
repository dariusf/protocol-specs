package main

import (
	"basic/rvp"
	"basic/rvq"
	"basic/rvr"
	"basic/rvt"
	"basic/rvu"
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

func checkT(step string, err error, m *rvt.Monitor, expectedSuccess bool) {
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

func checkU(step string, err error, m *rvu.Monitor, expectedSuccess bool) {
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

	parties := map[string]interface{}{"P": map[string]bool{"p1": true}}
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

	parties := map[string]interface{}{"Q": map[string]bool{"q1": true}}
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

	parties := map[string]interface{}{"R": map[string]bool{"r1": true}, "S": map[string]bool{"s1": true, "s2": true}}
	m := rvr.NewMonitor(parties)

	err := m.Step(rvr.Global{A: 1}, rvr.RChangeA1)
	checkR("start", err, m, true)

	err = m.StepA(rvr.RChangeA1)
	checkR("cannot move on before both parties 1", err, m, false)

	err = m.Step(rvr.Global{A: 1, History1: map[string]interface{}{"to": "s1", "type": "m"}}, rvr.RSendM2, "s1")
	checkR("first party", err, m, true)

	err = m.StepA(rvr.RChangeA1)
	checkR("cannot move on before both parties 2", err, m, false)

	err = m.Step(rvr.Global{A: 1, History1: map[string]interface{}{"to": "s2", "type": "m"}}, rvr.RSendM2, "s2")
	checkR("second party", err, m, true)

	err = m.Step(rvr.Global{A: 2, History1: map[string]interface{}{"to": "s2", "type": "m"}}, rvr.RChangeA3)
	checkR("final state change", err, m, true)

	m.PrintLog()
}

func testSelfSend() {

	parties := map[string]interface{}{"T": map[string]bool{"t1": true, "t2": true}, "Self": "t1"}
	m := rvt.NewMonitor(parties)

	// from the perspective of t1
	err := m.Step(rvt.Global{Parties: map[string]bool{}}, rvt.TChangeParties1)
	checkT("init", err, m, true)

	// explore the thread where we send first
	err = m.Step(rvt.Global{Parties: map[string]bool{}, History1: map[string]interface{}{"to": "t2", "type": "m"}}, rvt.TSendM2, "t2")
	checkT("send m2", err, m, true)

	err = m.Step(rvt.Global{Parties: map[string]bool{"t1": true}, History1: map[string]interface{}{"to": "t2", "type": "m"}}, rvt.TChangeParties3, "t2")
	checkT("add recipient to set", err, m, true)

	// explore the branch where we receive
	err = m.Step(rvt.Global{Parties: map[string]bool{"t1": true}, History1: map[string]interface{}{"from": "t2", "type": "m"}}, rvt.TReceiveM4, "t2")
	checkT("receive m4", err, m, true)

	err = m.Step(rvt.Global{Parties: map[string]bool{"t1": true, "t2": true}, History1: map[string]interface{}{"from": "t2", "type": "m"}}, rvt.TChangeParties5, "t2")
	checkT("add sender to set", err, m, true)

	m.PrintLog()
}

func testSelfSend1() {

	parties := map[string]interface{}{"U": map[string]bool{"u1": true, "u2": true}, "Self": "u2"}
	m := rvu.NewMonitor(parties)

	// from the perspective of u2
	err := m.Step(rvu.Global{Parties: map[string]bool{}}, rvu.UChangeParties1)
	checkU("start u", err, m, true)

	// explore the thread where we send and receive to/from self
	err = m.Step(rvu.Global{Parties: map[string]bool{}, History1: map[string]interface{}{"to": "u2", "type": "m"}}, rvu.USendM2, "t2")
	checkU("send m2", err, m, true)

	err = m.Step(rvu.Global{Parties: map[string]bool{}, History1: map[string]interface{}{"from": "u2", "type": "m"}}, rvu.UReceiveM3, "t2")
	checkU("receive m3", err, m, true)

	// only u2 should be in the set because we didn't involve u1
	err = m.Step(rvu.Global{Parties: map[string]bool{"u2": true}, History1: map[string]interface{}{"from": "u2", "type": "m"}}, rvu.UChangeParties4)
	checkU("add to set", err, m, true)

	m.PrintLog()
}

func main() {
	testDisj()
	fmt.Println("---")
	testPreamble()
	fmt.Println("---")
	testJoin()
	fmt.Println("---")
	testSelfSend()
	fmt.Println("---")
	testSelfSend1()
}
