
  $ ls

  $ protocol monitor --parties C,P <<EOF
  > forall c in C
  >   c.a = 1
  > ltl ([] (a > 0))
  > EOF
  monitorC.go

  $ ls
  monitorC.go

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
  
  // LTL property 0
  
  // Propositions
  func (l *LTLMonitor0) t0(g Global) bool {
  	return (g.A > 0)
  }
  
  type State0 int
  
  const (
  	S_0_R State0 = iota
  	S_1_Y
  )
  
  type LTLMonitor0 struct {
  	state     State0
  	succeeded bool
  	failed    bool
  	vars      map[string]map[string]bool
  }
  
  func NewLTLMonitor0(vars map[string]map[string]bool) *LTLMonitor0 {
  	return &LTLMonitor0{
  		vars:      vars,
  		state:     S_1_Y,
  		succeeded: false,
  		failed:    false,
  	}
  }
  
  func (l *LTLMonitor0) StepLTL0(g Global) error {
  	if l.succeeded {
  		return nil
  	} else if l.failed {
  		return errors.New("property falsified")
  	}
  
  	// evaluate all the props
  	t0 := l.t0(g)
  
  	// note the true ones, take that transition
  	switch l.state {
  	case S_0_R:
  		if t0 {
  			l.state = S_0_R
  			l.failed = true
  			return errors.New("property falsified")
  		} else {
  			l.state = S_0_R
  			l.failed = true
  			return errors.New("property falsified")
  		}
  	case S_1_Y:
  		if t0 {
  			l.state = S_1_Y
  			return nil
  		} else {
  			l.state = S_0_R
  			l.failed = true
  			return errors.New("property falsified")
  		}
  	default:
  		panic("invalid state")
  	}
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
  	vars            map[string]map[string]bool
  	ltlMonitor0     *LTLMonitor0
  	Log             Log
  	ExecutionTimeNs int64
  	lock            sync.Mutex
  }
  
  //func NewMonitor(vars map[string][]string) *Monitor {
  func NewMonitor(vars map[string]map[string]bool) *Monitor {
  	return &Monitor{
  		// previous is the empty Global
  		PC:          map[string]int{}, // not the smae as a nil map
  		vars:        vars,
  		ltlMonitor0: NewLTLMonitor0(vars),
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
  	m.ltlMonitor0 = NewLTLMonitor0(m.vars)
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
  
  	if err := m.ltlMonitor0.StepLTL0(g); err != nil {
  		return err
  	}
  
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
  
  	if err := m.ltlMonitor0.StepLTL0(g); err != nil {
  		return err
  	}
  
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
