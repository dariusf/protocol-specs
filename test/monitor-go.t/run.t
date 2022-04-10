
  $ protocol print <<EOF
  > party c in C (c.b = 0)
  > forall c in C
  >   c.b > 0 =>
  >     c.b = 1
  > EOF
  (forall c in C
     c.b = 0);
  (forall c in C
     c.b > 0 =>
       c.b = 1)

  $ protocol print --project C <<EOF
  > party c in C (c.b = 0)
  > forall c in C
  >   c.b > 0 =>
  >     c.b = 1
  > EOF
  b = 0;
  (b > 0 =>
     b = 1)

  $ protocol print --actions --project C <<EOF
  > party c in C (c.b = 0)
  > forall c in C
  >   c.b > 0 =>
  >     c.b = 1
  > EOF
  digraph G {
    1 [label="CChangeB1\n{start(Cmain)}\nb = 0\n{Cmain = 1}\n"];
    2 [label="CChangeB2\n{Cmain = 1}\nb = 1\n{Cmain = 2}\n"];
    1 -> 2;
  }

  $ protocol monitor <<EOF
  > party c in C (c.b = 0)
  > forall c in C
  >   c.b > 0 =>
  >     c.b = 1
  > EOF
  monitorC.go

  $ sed -n '/func.*precondition/,/^}/p' monitorC.go
  func (m *Monitor) precondition(g *Global, action Action, params ...string) error {
  	switch action {
  	case CChangeB1:
  		// no params check
  		// no logical preconditions
  		if !(m.PC["Cmain"] == 0) {
  			return fmt.Errorf("control precondition of CChangeB1 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeB1", params: params})
  		return nil
  	case CChangeB2:
  		// no params check
  		if g != nil && !(g.B > 0) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CChangeB2", params)
  		}
  		if !(m.PC["Cmain"] == 1) {
  			return fmt.Errorf("control precondition of CChangeB2 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeB2", params: params})
  		return nil
  	default:
  		panic("invalid action")
  	}
  }

  $ sed -n '/func.*applyControlPostcondition/,/^}/p' monitorC.go
  func (m *Monitor) applyControlPostcondition(action Action, params ...string) error {
  	switch action {
  	case CChangeB1:
  		// no params check
  		m.PC["Cmain"] = 1
  	case CChangeB2:
  		// no params check
  		m.PC["Cmain"] = 2
  	default:
  		panic("invalid action")
  	}
  	return nil
  }

  $ protocol monitor <<EOF
  > party c in C (c.a = 1)
  > forall c in C
  >   c.a = 1
  > ltl ([] (a > 0))
  > EOF
  monitorC.go

  $ sed -n '/func.*precondition/,/^}/p' monitorC.go
  func (m *Monitor) precondition(g *Global, action Action, params ...string) error {
  	switch action {
  	case CChangeA1:
  		// no params check
  		// no logical preconditions
  		if !(m.PC["Cmain"] == 0) {
  			return fmt.Errorf("control precondition of CChangeA1 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeA1", params: params})
  		return nil
  	default:
  		panic("invalid action")
  	}
  }

  $ sed -n '/func.*applyControlPostcondition/,/^}/p' monitorC.go
  func (m *Monitor) applyControlPostcondition(action Action, params ...string) error {
  	switch action {
  	case CChangeA1:
  		// no params check
  		m.PC["Cmain"] = 2
  	default:
  		panic("invalid action")
  	}
  	return nil
  }
