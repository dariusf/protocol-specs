
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
  )
  
  type Global struct {
  	A int
  }
  
  func (m *Monitor) t0(g Global) bool {
  	return (g.A > 0)
  }
  
  type State int
  
  const (
  	S_0_R State = iota
  	S_1_Y
  )
  
  type Action int
  
  const (
  	CChangeA0 Action = iota
  )
  
  func (m *Monitor) precondition(action Action) bool {
  	switch action {
  	case CChangeA0:
  		return true
  	default:
  		panic("invalid action")
  	}
  }
  
  func (m *Monitor) applyPostcondition(action Action) {
  	switch action {
  	case CChangeA0:
  		m.pc = 0
  	default:
  		panic("invalid action")
  	}
  }
  
  type Monitor struct {
  	state    State
  	previous Global
  	done     bool
  	dead     bool
  	pc       int
  	//vars     map[string][]string
  	vars map[string]map[string]bool
  }
  
  //func NewMonitor(vars map[string][]string) *Monitor {
  func NewMonitor(vars map[string]map[string]bool) *Monitor {
  	return &Monitor{
  		state: S_1_Y,
  		// previous is the empty Global
  		done: false,
  		dead: false,
  		pc:   -1,
  		vars: vars,
  	}
  }
  
  // For debugging
  func (m *Monitor) InternalState() State {
  	return m.state
  }
  
  func (m *Monitor) Step(g Global, act Action) error {
  	if m.done {
  		return nil
  	} else if m.dead {
  		return errors.New("sink state")
  	}
  
  	if !m.precondition(act) {
  		return errors.New("precondition violation")
  	}
  
  	m.previous = g
  
  	m.applyPostcondition(act)
  
  	// evaluate all the props
  	t0 := m.t0(g)
  
  	// note the true ones, take that transition
  	switch m.state {
  	case S_0_R:
  		if t0 {
  			m.state = S_0_R
  			m.dead = true
  			return errors.New("sink state")
  		} else {
  			m.state = S_0_R
  			m.dead = true
  			return errors.New("sink state")
  		}
  
  	case S_1_Y:
  		if t0 {
  			m.state = S_1_Y
  			return nil
  		} else {
  			m.state = S_0_R
  			m.dead = true
  			return errors.New("sink state")
  		}
  
  	default:
  		panic("invalid state")
  	}
  }
