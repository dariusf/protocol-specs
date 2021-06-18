
  $ ls
  run.t

  $ protocol monitor --parties C,P <<EOF
  > forall c in C
  >   c.a = 1
  > ltl ([] (a > 0))
  > EOF
  monitorC.go

  $ ls
  monitorC.go
  run.t

  $ cat monitorC.go
  package rv
  
  import (
  	"errors"
  	"fmt"
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
  			return errors.New("control precondition violated")
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
  	vars        map[string]map[string]bool
  	ltlMonitor0 *LTLMonitor0
  	Log         Log
  }
  
  //func NewMonitor(vars map[string][]string) *Monitor {
  func NewMonitor(vars map[string]map[string]bool) *Monitor {
  	return &Monitor{
  		// previous is the empty Global
  		PC:          map[string]int{},
  		vars:        vars,
  		Log:         Log{},
  		ltlMonitor0: NewLTLMonitor0(vars),
  	}
  }
  
  func (m *Monitor) Step(g Global, act Action, params ...string) error {
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
  	if err := m.precondition(nil, act, params...); err != nil {
  		return err
  	}
  
  	if err := m.applyPostcondition(act, params...); err != nil {
  		return err
  	}
  
  	return nil
  }
  
  func (m *Monitor) StepS(g Global) error {
  
  	m.previous = g
  
  	// LTL monitors
  
  	if err := m.ltlMonitor0.StepLTL0(g); err != nil {
  		return err
  	}
  
  	return nil
  }
  
  func (m *Monitor) PrintLog() {
  	for _, e := range m.Log {
  		fmt.Printf("%v %v\n", e.action, e.params)
  	}
  }
