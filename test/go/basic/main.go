package main

import (
	"basic/rvc"
	"basic/rvp"
	"fmt"
)

func checkC(step string, err error, m *rvc.Monitor, expectedSuccess bool) {
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

func tryC() {

	parties := map[string]map[string]bool{"P": {"p1": true}, "C": {"c1": true}}
	m := rvc.NewMonitor(parties)

	err := m.StepA(rvc.CSendM8, "p2")
	checkC("send 1", err, m, true)
	// nonexistent party is allowed because there's nothing after to blow this up

	// repeat
	err = m.StepA(rvc.CSendM8, "p1")
	checkC("send 2", err, m, true)
	// this doesn't fail

	err = m.StepA(rvc.CSendM8, "p1")
	checkC("send 3", err, m, false)
	// now this fails

	m.PrintLog()
}

func tryP() {

	parties := map[string]map[string]bool{"P": {"p1": true}, "C": {"c1": true}}
	m := rvp.NewMonitor(parties)

	err := m.StepA(rvp.PReceiveM4, "c1")
	checkP("recv", err, m, true)

	err = m.StepA(rvp.PChangeA1)
	checkP("change 1", err, m, true)

	// violation
	err = m.StepA(rvp.PReceiveM4, "c1")
	checkP("ERROR recv again", err, m, false)

	err = m.StepA(rvp.PChangeA1)
	checkP("change 2", err, m, true)

	m.PrintLog()
}

func main() {
	tryC()
	fmt.Println("---")
	tryP()
}
