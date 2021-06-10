The classic two-phase commit protocol.

  $ protocol print 2pc.spec
  forall c in C
    (forall p in P
       c->p: prepare;
       (p->c: prepared;
        responded = union(responded, {p})
        \/
        p->c: abort;
        aborted = union(aborted, {p})));
    (aborted == {} =>
       (forall p in P
          c->p: commit;
          p->c: commit_ack)
     \/
     aborted != {} =>
       (forall p in P
          c->p: abort;
          p->c: abort_ack))

  $ protocol print 2pc-wait.spec
  forall c in C
    forall p in P
      c->p: prepare;
      (p->c: prepared;
       responded = union(responded, {p})
       \/
       p->c: abort;
       aborted = union(aborted, {p}))
  ||
  responded == P =>*
    (forall p in P
       c->p: commit;
       p->c: commit_ack)
  \/
  aborted != {} =>*
    (forall p in P
       c->p: abort;
       p->c: abort_ack)

  $ protocol print --parties P,C --types 2pc.spec
  forall (c : party C;global) in (C : {party C};global)
    (forall (p : party P;global) in (P : {party P};global)
       (c : party C;global)->(p : party P;global): prepare;
       ((p : party P;P)->(c : party C;P): prepared;
        (responded : {party P};C) = union((responded : {party P};C), {(p : party P;C)})
        \/
        (p : party P;P)->(c : party C;P): abort;
        (aborted : {party P};C) = union((aborted : {party P};C), {(p : party P;C)})));
    ((aborted : {party P};C) == {} =>
       (forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global): commit;
          (p : party P;P)->(c : party C;P): commit_ack)
     \/
     (aborted : {party P};C) != {} =>
       (forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global): abort;
          (p : party P;P)->(c : party C;P): abort_ack))

  $ protocol print 2pc.spec --parties C,P --project C
  (forall p in P
     ->p: prepare;
     (p->: prepared;
      responded = union(responded, {p})
      \/
      p->: abort;
      aborted = union(aborted, {p})));
  (aborted == {} =>
     (forall p in P
        ->p: commit;
        p->: commit_ack)
   \/
   aborted != {} =>
     (forall p in P
        ->p: abort;
        p->: abort_ack))

  $ protocol print 2pc.spec --parties C,P --project P
  forall c in C
    c->: prepare;
    (->c: prepared
     \/
     ->c: abort);
    (c->: commit;
     ->c: commit_ack
     \/
     c->: abort;
     ->c: abort_ack)

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && git diff --no-index 2pc1.spec 2pc2.spec

  $ protocol print 2pc-wait.spec > 2pc1-wait.spec && protocol print 2pc1-wait.spec | protocol print > 2pc2-wait.spec && git diff --no-index 2pc1-wait.spec 2pc2-wait.spec

  $ protocol print 2pc.spec --parties C,P --project P --actions
  digraph G {
    0 [label="PReceivePrepare0\ntid: Pt0(c:C)\n{start}\nλ [(c:C)].\nc->: prepare"];
    1 [label="PSendPrepared1\ntid: Pt0(c:C)\n{Pt0(c:C) = 0}\nλ [(c:C)].\n->c: prepared"];
    2 [label="PSendAbort2\ntid: Pt0(c:C)\n{Pt0(c:C) = 0}\nλ [(c:C)].\n->c: abort"];
    3 [label="PReceiveCommit3\ntid: Pt0(c:C)\n{Any(Pt0(c:C) = 1, Pt0(c:C) = 2)}\nλ [(c:C)].\nc->: commit"];
    4 [label="PSendCommitAck4\ntid: Pt0(c:C)\n{Pt0(c:C) = 3}\nλ [(c:C)].\n->c: commit_ack"];
    5 [label="PReceiveAbort5\ntid: Pt0(c:C)\n{Any(Pt0(c:C) = 1, Pt0(c:C) = 2)}\nλ [(c:C)].\nc->: abort"];
    6 [label="PSendAbortAck6\ntid: Pt0(c:C)\n{Pt0(c:C) = 5}\nλ [(c:C)].\n->c: abort_ack"];
    5 -> 6;
    3 -> 4;
    2 -> 5;
    2 -> 3;
    1 -> 5;
    1 -> 3;
    0 -> 2;
    0 -> 1;
  }

  $ protocol print 2pc.spec --parties C,P --project C --actions
  digraph G {
    0 [label="CSendPrepare0\ntid: Ct0(p:P)\n{start}\nλ [(p:P)].\n->p: prepare"];
    1 [label="CReceivePrepared1\ntid: Ct0(p:P)\n{Ct0(p:P) = 0}\nλ [(p:P)].\np->: prepared;\nresponded = union(responded, {p})"];
    2 [label="CReceiveAbort2\ntid: Ct0(p:P)\n{Ct0(p:P) = 0}\nλ [(p:P)].\np->: abort;\naborted = union(aborted, {p})"];
    3 [label="CSendCommit3\ntid: Ct2(p:P)\n{∀ p:P. Any(Ct0(p:P) = 1, Ct0(p:P) = 2)}\n{[aborted == {}]}\nλ [(p:P)].\n->p: commit"];
    4 [label="CReceiveCommitAck4\ntid: Ct2(p:P)\n{Ct2(p:P) = 3}\nλ [(p:P)].\np->: commit_ack"];
    5 [label="CSendAbort5\ntid: Ct1(p:P)\n{∀ p:P. Any(Ct0(p:P) = 1, Ct0(p:P) = 2)}\n{[aborted != {}]}\nλ [(p:P)].\n->p: abort"];
    6 [label="CReceiveAbortAck6\ntid: Ct1(p:P)\n{Ct1(p:P) = 5}\nλ [(p:P)].\np->: abort_ack"];
    5 -> 6;
    3 -> 4;
    2 -> 5;
    2 -> 3;
    1 -> 5;
    1 -> 3;
    0 -> 2;
    0 -> 1;
  }

  $ protocol tla 2pc.spec --parties C,P
  2pc.tla
  2pc.cfg

  $ cat 2pc.tla
  
  --------------------------------- MODULE 2pc ---------------------------------
  
  EXTENDS Integers, FiniteSets, Sequences, TLC
  
  VARIABLE messages
  
  Send(m, msgs) ==
      IF m \in DOMAIN msgs THEN
          [msgs EXCEPT ![m] = msgs[m] + 1]
      ELSE
          msgs @@ (m :> 1)
  
  Receive(m, msgs) ==
      IF m \in DOMAIN msgs THEN
          [msgs EXCEPT ![m] = msgs[m] - 1]
      ELSE
          msgs
  
  VARIABLE pc
  
  
  CONSTANTS C, P
  
  CONSTANTS c1, p1, p2
  
  CONSTANTS Ct0, Ct2, Ct1, Pt0
  
  CONSTANTS prepare, prepared, commit, commit_ack, abort, abort_ack
  
  \* Used by C
  
  VARIABLES responded, aborted
  
  Cvars == <<responded, aborted>>
  
  Pvars == <<>>
  
  vars == <<responded, aborted, messages, pc>>
  
  threads == {Ct0, Ct2, Ct1, Pt0}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, <<Ct2, p2>>, <<Ct2, p1>>, <<Ct1, p2>>, <<Ct1, p1>>, <<Pt0, c1>>}
  
  Init ==
    /\ responded = [i \in C |-> {}]
    /\ aborted = [i \in C |-> {}]
    /\ messages = [i \in {} |-> 0]
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> -1]]
  
  CSendPrepare0(self, p) ==
    /\ pc[self][<<Ct0, p>>] = -1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 0]]
    /\ 
      /\ messages' = Send([mtype |-> prepare, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CReceivePrepared1(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 1]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = prepared
      /\ m.mdest = self
      /\ responded' = [responded EXCEPT ![self] = (responded[self] \union {p})]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<aborted>>
  
  CReceiveAbort2(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 2]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ aborted' = [aborted EXCEPT ![self] = (aborted[self] \union {p})]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded>>
  
  CSendCommit3(self, p) ==
    /\ \A pi \in P : 
      \/ pc[self][<<Ct0, p>>] = 1
      \/ pc[self][<<Ct0, p>>] = 2
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 3]]
    /\ 
      /\ messages' = Send([mtype |-> commit, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CReceiveCommitAck4(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 4]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = commit_ack
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CSendAbort5(self, p) ==
    /\ \A pi \in P : 
      \/ pc[self][<<Ct0, p>>] = 1
      \/ pc[self][<<Ct0, p>>] = 2
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 5]]
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CReceiveAbortAck6(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 5
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 6]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort_ack
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceivePrepare7(self, c) ==
    /\ pc[self][<<Pt0, c>>] = -1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 7]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendPrepared8(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 7
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 8]]
    /\ 
      /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendAbort9(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 7
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 9]]
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceiveCommit10(self, c) ==
    /\ 
      \/ pc[self][<<Pt0, c>>] = 8
      \/ pc[self][<<Pt0, c>>] = 9
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 10]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = commit
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendCommitAck11(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 10
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 11]]
    /\ 
      /\ messages' = Send([mtype |-> commit_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceiveAbort12(self, c) ==
    /\ 
      \/ pc[self][<<Pt0, c>>] = 8
      \/ pc[self][<<Pt0, c>>] = 9
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 12]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendAbortAck13(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 12
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 13]]
    /\ 
      /\ messages' = Send([mtype |-> abort_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  Next ==
    \/ \E self \in C : \E p \in P : CSendPrepare0(self, p)
    \/ \E self \in C : \E p \in P : CReceivePrepared1(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbort2(self, p)
    \/ \E self \in C : \E p \in P : CSendCommit3(self, p)
    \/ \E self \in C : \E p \in P : CReceiveCommitAck4(self, p)
    \/ \E self \in C : \E p \in P : CSendAbort5(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbortAck6(self, p)
    \/ \E self \in P : \E c \in C : PReceivePrepare7(self, c)
    \/ \E self \in P : \E c \in C : PSendPrepared8(self, c)
    \/ \E self \in P : \E c \in C : PSendAbort9(self, c)
    \/ \E self \in P : \E c \in C : PReceiveCommit10(self, c)
    \/ \E self \in P : \E c \in C : PSendCommitAck11(self, c)
    \/ \E self \in P : \E c \in C : PReceiveAbort12(self, c)
    \/ \E self \in P : \E c \in C : PSendAbortAck13(self, c)
  
  Spec == Init /\ [][Next]_vars
  
  ===============================================================================

  $ protocol monitor --parties C,P 2pc.spec
  monitorC.go

  $ cat monitorC.go
  package rv
  
  import (
  	"errors"
  	"reflect"
  )
  
  type Global struct {
  	Responded map[string]bool
  	Aborted   map[string]bool
  }
  
  func (m *Monitor) t0(g Global) bool {
  	return (!reflect.DeepEqual(g.Aborted, map[string]bool{}) || reflect.DeepEqual(g.Responded, m.vars["P"]))
  }
  
  type State int
  
  const (
  	S_0_Y State = iota
  	S_1_G
  )
  
  type Action int
  
  const (
  	CSendPrepare0 Action = iota
  	CReceivePrepared1
  	CReceiveAbort2
  	CSendCommit3
  	CReceiveCommitAck4
  	CSendAbort5
  	CReceiveAbortAck6
  )
  
  func (m *Monitor) precondition(action Action) bool {
  	switch action {
  	case CSendPrepare0:
  		return true
  	case CReceivePrepared1:
  		return m.pc == 0
  	case CReceiveAbort2:
  		return m.pc == 0
  	case CSendCommit3:
  		return m.pc == 2 || m.pc == 1
  	case CReceiveCommitAck4:
  		return m.pc == 3
  	case CSendAbort5:
  		return m.pc == 2 || m.pc == 1
  	case CReceiveAbortAck6:
  		return m.pc == 5
  	default:
  		panic("invalid action")
  	}
  }
  
  func (m *Monitor) applyPostcondition(action Action) {
  	switch action {
  	case CSendPrepare0:
  		m.pc = 0
  	case CReceivePrepared1:
  		m.pc = 1
  	case CReceiveAbort2:
  		m.pc = 2
  	case CSendCommit3:
  		m.pc = 3
  	case CReceiveCommitAck4:
  		m.pc = 4
  	case CSendAbort5:
  		m.pc = 5
  	case CReceiveAbortAck6:
  		m.pc = 6
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
  		state: S_0_Y,
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
  	case S_0_Y:
  		if t0 {
  			m.state = S_1_G
  			m.done = true
  			return nil
  		} else {
  			m.state = S_0_Y
  			return nil
  		}
  
  	case S_1_G:
  		if t0 {
  			m.state = S_1_G
  			m.done = true
  			return nil
  		} else {
  			m.state = S_1_G
  			m.done = true
  			return nil
  		}
  
  	default:
  		panic("invalid state")
  	}
  }
