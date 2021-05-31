
  $ ls
  run.t

  $ protocol monitor --parties C,P --project C <<EOF
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
  
  func t0(g Global) bool {
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
  
  func precondition(action Action) bool {
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
  }
  
  func NewMonitor() *Monitor {
  	return &Monitor{state: S_1_Y, pc: -1}
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
  
  	if !precondition(act) {
  		return errors.New("precondition violation")
  	}
  
  	m.previous = g
  
  	m.applyPostcondition(act)
  
  	// evaluate all the props
  	t0 := t0(g)
  	println("t0", t0)
  
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
