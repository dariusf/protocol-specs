
  $ ls

  $ protocol monitor <<EOF
  > party c in C ()
  > party p in P ()
  > forall c in C
  >   c.a = 1
  > ltl ([] (a > 0))
  > EOF
  monitorC.go

  $ ls
  actions.txt
  monitorC.go
  types.txt

  $ cat monitorC.go
  package rvc
  
  import (
  	"errors"
  	"fmt"
  	"sync"
  	"time"
  )
  
  type Global struct {
  	A int
  }
  
  type Action int
  
  const (
  	CChangeA1 Action = iota
  )
  
  func all(s []string, f func(string) bool) bool {
  	b := true
  	for _, v := range s {
  		b = b && f(v)
  	}
  	return b
  }
  
  func allSet(s map[string]bool, f func(string) bool) bool {
  	b := true
  	for k := range s {
  		b = b && f(k)
  	}
  	return b
  }
  
  func any(s []string, f func(string) bool) bool {
  	b := false
  	for _, v := range s {
  		b = b || f(v)
  	}
  	return b
  }
  
  func anySet(s map[string]bool, f func(string) bool) bool {
  	b := false
  	for k := range s {
  		b = b || f(k)
  	}
  	return b
  }
  
  func (m *Monitor) precondition(g *Global, action Action, params ...string) error {
  	switch action {
  	case CChangeA1:
  
  		// no preconditions
  		if !(m.PC[Cmain] == 0) {
  			return fmt.Errorf("control precondition of CChangeA1 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeA1", params: params})
  		return nil
  	default:
  		panic("invalid action")
  	}
  }
  
  func (m *Monitor) applyPostcondition(action Action, params ...string) error {
  	switch action {
  	case CChangeA1:
  
  		m.PC[Cmain] = 1
  	default:
  		panic("invalid action")
  	}
  	return nil
  }
  
  type entry struct {
  	action string
  	params []string
  }
  
  type Log = []entry
  
  type Monitor struct {
  	previous Global
  	PC       map[string]int
  	//vars     map[string][]string
  	vars map[string]map[string]bool
  
  	Log             Log
  	ExecutionTimeNs int64
  	lock            sync.Mutex
  }
  
  //func NewMonitor(vars map[string][]string) *Monitor {
  func NewMonitor(vars map[string]map[string]bool) *Monitor {
  	return &Monitor{
  		// previous is the empty Global
  		PC:   map[string]int{}, // not the smae as a nil map
  		vars: vars,
  
  		// Everything else uses mzero
  	}
  }
  
  func (m *Monitor) Reset() {
  	m.lock.Lock()
  	defer m.lock.Unlock()
  	defer m.trackTime(time.Now())
  
  	m.previous = Global{}
  	m.PC = map[string]int{}
  	// vars ok
  
  	m.Log = Log{}
  
  	// This is deliberately not reset, to track the total time the monitor has been used
  	// m.ExecutionTimeNs = 0
  
  	// lock ok
  }
  
  func (m *Monitor) Step(g Global, act Action, params ...string) error {
  	m.lock.Lock()
  	defer m.lock.Unlock()
  	defer m.trackTime(time.Now())
  
  	if err := m.precondition(&g, act, params...); err != nil {
  		return err
  	}
  
  	m.previous = g
  
  	if err := m.applyPostcondition(act, params...); err != nil {
  		return err
  	}
  
  	// LTL monitors
  
  	return nil
  }
  
  func (m *Monitor) StepA(act Action, params ...string) error {
  	m.lock.Lock()
  	defer m.lock.Unlock()
  	defer m.trackTime(time.Now())
  
  	if err := m.precondition(nil, act, params...); err != nil {
  		return err
  	}
  
  	if err := m.applyPostcondition(act, params...); err != nil {
  		return err
  	}
  
  	return nil
  }
  
  func (m *Monitor) StepS(g Global) error {
  	m.lock.Lock()
  	defer m.lock.Unlock()
  	defer m.trackTime(time.Now())
  
  	m.previous = g
  
  	// LTL monitors
  
  	return nil
  }
  
  func (m *Monitor) PrintLog() {
  	m.lock.Lock()
  	defer m.lock.Unlock()
  
  	for _, e := range m.Log {
  		fmt.Printf("%s %v\n", e.action, e.params)
  	}
  	// fmt.Printf("Monitor time taken: %v\n", time.Duration(m.ExecutionTimeNs))
  	fmt.Printf("Monitor time taken: %d\n", m.ExecutionTimeNs)
  }
  
  func (m *Monitor) trackTime(start time.Time) {
  	elapsed := time.Since(start)
  	m.ExecutionTimeNs += elapsed.Nanoseconds()
  }
