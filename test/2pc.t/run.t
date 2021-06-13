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
    1 [label="PReceivePrepare1\ntid: Pt0(c:C)\n{start}\nthis: {Pt0(c:C) = 1}\nparams: [(c:C)]\nc->: prepare"];
    2 [label="PSendPrepared2\ntid: Pt0(c:C)\n{Pt0(c:C) = 1}\nthis: {Pt0(c:C) = 2}\nparams: [(c:C)]\n->c: prepared"];
    3 [label="PSendAbort3\ntid: Pt0(c:C)\n{Pt0(c:C) = 1}\nthis: {Pt0(c:C) = 3}\nparams: [(c:C)]\n->c: abort"];
    4 [label="PReceiveCommit4\ntid: Pt0(c:C)\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nthis: {Pt0(c:C) = 4}\nparams: [(c:C)]\nc->: commit"];
    5 [label="PSendCommitAck5\ntid: Pt0(c:C)\n{Pt0(c:C) = 4}\nthis: {Pt0(c:C) = 5}\nparams: [(c:C)]\n->c: commit_ack"];
    6 [label="PReceiveAbort6\ntid: Pt0(c:C)\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nthis: {Pt0(c:C) = 6}\nparams: [(c:C)]\nc->: abort"];
    7 [label="PSendAbortAck7\ntid: Pt0(c:C)\n{Pt0(c:C) = 6}\nthis: {Pt0(c:C) = 7}\nparams: [(c:C)]\n->c: abort_ack"];
    6 -> 7;
    4 -> 5;
    3 -> 6;
    3 -> 4;
    2 -> 6;
    2 -> 4;
    1 -> 3;
    1 -> 2;
  }

  $ protocol print 2pc.spec --parties C,P --project C --actions
  digraph G {
    1 [label="CSendPrepare1\ntid: Ct0(p:P)\n{start}\nthis: {Ct0(p:P) = 1}\nparams: [(p:P)]\n->p: prepare"];
    2 [label="CReceivePrepared2\ntid: Ct0(p:P)\n{Ct0(p:P) = 1}\nthis: {Ct0(p:P) = 2}\nparams: [(p:P)]\np->: prepared;\nresponded = union(responded, {p})"];
    3 [label="CReceiveAbort3\ntid: Ct0(p:P)\n{Ct0(p:P) = 1}\nthis: {Ct0(p:P) = 3}\nparams: [(p:P)]\np->: abort;\naborted = union(aborted, {p})"];
    4 [label="CSendCommit4\ntid: Ct2(p:P)\n{∀ p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 3)}\nthis: {Ct2(p:P) = 4}\n{[aborted == {}]}\nparams: [(p:P)]\n->p: commit"];
    5 [label="CReceiveCommitAck5\ntid: Ct2(p:P)\n{Ct2(p:P) = 4}\nthis: {Ct2(p:P) = 5}\nparams: [(p:P)]\np->: commit_ack"];
    6 [label="CSendAbort6\ntid: Ct1(p:P)\n{∀ p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 3)}\nthis: {Ct1(p:P) = 6}\n{[aborted != {}]}\nparams: [(p:P)]\n->p: abort"];
    7 [label="CReceiveAbortAck7\ntid: Ct1(p:P)\n{Ct1(p:P) = 6}\nthis: {Ct1(p:P) = 7}\nparams: [(p:P)]\np->: abort_ack"];
    6 -> 7;
    4 -> 5;
    3 -> 6;
    3 -> 4;
    2 -> 6;
    2 -> 4;
    1 -> 3;
    1 -> 2;
  }

  $ protocol tla 2pc.spec --parties C:1,P:2
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
  
  VARIABLE history
  
  CONSTANTS C, P
  
  CONSTANTS c1, p1, p2
  
  CONSTANTS Ct0, Ct2, Ct1, Pt0
  
  CONSTANTS prepare, prepared, commit, commit_ack, abort, abort_ack
  
  Symmetry == (Permutations(C) \union Permutations(P))
  
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
    /\ history = <<>>
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> 0]]
  
  CSendPrepare1(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 1]]
    /\ history' = Append(<<"CSendPrepare1", p>>, history)
    /\ 
      /\ messages' = Send([mtype |-> prepare, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CReceivePrepared2(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 2]]
    /\ history' = Append(<<"CReceivePrepared2", p>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = prepared
      /\ m.mdest = self
      /\ responded' = [responded EXCEPT ![self] = (responded[self] \union {p})]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<aborted>>
  
  CReceiveAbort3(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 3]]
    /\ history' = Append(<<"CReceiveAbort3", p>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ aborted' = [aborted EXCEPT ![self] = (aborted[self] \union {p})]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded>>
  
  CSendCommit4(self, p) ==
    /\ \A pi \in P : 
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 4]]
    /\ history' = Append(<<"CSendCommit4", p>>, history)
    /\ 
      /\ messages' = Send([mtype |-> commit, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CReceiveCommitAck5(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 5]]
    /\ history' = Append(<<"CReceiveCommitAck5", p>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = commit_ack
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CSendAbort6(self, p) ==
    /\ \A pi \in P : 
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 6]]
    /\ history' = Append(<<"CSendAbort6", p>>, history)
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  CReceiveAbortAck7(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 6
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 7]]
    /\ history' = Append(<<"CReceiveAbortAck7", p>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort_ack
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceivePrepare8(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 8]]
    /\ history' = Append(<<"PReceivePrepare8", c>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendPrepared9(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 8
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 9]]
    /\ history' = Append(<<"PSendPrepared9", c>>, history)
    /\ 
      /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendAbort10(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 8
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 10]]
    /\ history' = Append(<<"PSendAbort10", c>>, history)
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceiveCommit11(self, c) ==
    /\ 
      \/ pc[self][<<Pt0, c>>] = 9
      \/ pc[self][<<Pt0, c>>] = 10
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 11]]
    /\ history' = Append(<<"PReceiveCommit11", c>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = commit
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendCommitAck12(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 11
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 12]]
    /\ history' = Append(<<"PSendCommitAck12", c>>, history)
    /\ 
      /\ messages' = Send([mtype |-> commit_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceiveAbort13(self, c) ==
    /\ 
      \/ pc[self][<<Pt0, c>>] = 9
      \/ pc[self][<<Pt0, c>>] = 10
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 13]]
    /\ history' = Append(<<"PReceiveAbort13", c>>, history)
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendAbortAck14(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 13
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 14]]
    /\ history' = Append(<<"PSendAbortAck14", c>>, history)
    /\ 
      /\ messages' = Send([mtype |-> abort_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<responded, aborted>>
  
  Next ==
    \/ \E self \in C : \E p \in P : CSendPrepare1(self, p)
    \/ \E self \in C : \E p \in P : CReceivePrepared2(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbort3(self, p)
    \/ \E self \in C : \E p \in P : CSendCommit4(self, p)
    \/ \E self \in C : \E p \in P : CReceiveCommitAck5(self, p)
    \/ \E self \in C : \E p \in P : CSendAbort6(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbortAck7(self, p)
    \/ \E self \in P : \E c \in C : PReceivePrepare8(self, c)
    \/ \E self \in P : \E c \in C : PSendPrepared9(self, c)
    \/ \E self \in P : \E c \in C : PSendAbort10(self, c)
    \/ \E self \in P : \E c \in C : PReceiveCommit11(self, c)
    \/ \E self \in P : \E c \in C : PSendCommitAck12(self, c)
    \/ \E self \in P : \E c \in C : PReceiveAbort13(self, c)
    \/ \E self \in P : \E c \in C : PSendAbortAck14(self, c)
  
  Spec == Init /\ [][Next]_<<vars, history>>
  
  ===============================================================================

  $ cat 2pc.cfg
  
  CONSTANTS
    C = {c1}
    c1 = c1
    P = {p1, p2}
    p1 = p1
    p2 = p2
    prepare = prepare
    prepared = prepared
    commit = commit
    commit_ack = commit_ack
    abort = abort
    abort_ack = abort_ack
    Ct0 = Ct0
    Ct2 = Ct2
    Ct1 = Ct1
    Pt0 = Pt0
  SYMMETRY Symmetry
  SPECIFICATION Spec
  VIEW vars
  \* INVARIANT Inv

  $ protocol monitor --parties C,P 2pc.spec
  monitorC.go
  monitorP.go

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
  
  type Action int
  
  const (
  	CSendPrepare1 Action = iota
  	CReceivePrepared2
  	CReceiveAbort3
  	CSendCommit4
  	CReceiveCommitAck5
  	CSendAbort6
  	CReceiveAbortAck7
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
  	case CSendPrepare1:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct0_"+(params[0] /* p : P */)] == 0) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	case CReceivePrepared2:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct0_"+(params[0] /* p : P */)] == 1) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	case CReceiveAbort3:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct0_"+(params[0] /* p : P */)] == 1) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	case CSendCommit4:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(reflect.DeepEqual(g.Aborted, map[string]bool{})) {
  			return errors.New("logical precondition violated")
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 3 })) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	case CReceiveCommitAck5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct2_"+(params[0] /* p : P */)] == 4) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	case CSendAbort6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(!reflect.DeepEqual(g.Aborted, map[string]bool{})) {
  			return errors.New("logical precondition violated")
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 3 })) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	case CReceiveAbortAck7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct1_"+(params[0] /* p : P */)] == 6) {
  			return errors.New("control precondition violated")
  		}
  		return nil
  	default:
  		panic("invalid action")
  	}
  }
  
  func (m *Monitor) applyPostcondition(action Action, params ...string) error {
  	switch action {
  	case CSendPrepare1:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct0_"+(params[0] /* p : P */)] = 1
  	case CReceivePrepared2:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct0_"+(params[0] /* p : P */)] = 2
  	case CReceiveAbort3:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct0_"+(params[0] /* p : P */)] = 3
  	case CSendCommit4:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 4
  	case CReceiveCommitAck5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 5
  	case CSendAbort6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 6
  	case CReceiveAbortAck7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 7
  	default:
  		panic("invalid action")
  	}
  	return nil
  }
  
  // LTL property 0
  
  // Propositions
  func (l *LTLMonitor0) t0(g Global) bool {
  	return (!reflect.DeepEqual(g.Aborted, map[string]bool{}) || reflect.DeepEqual(g.Responded, l.vars["P"]))
  }
  
  type State0 int
  
  const (
  	S_0_Y State0 = iota
  	S_1_G
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
  		state:     S_0_Y,
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
  	case S_0_Y:
  		if t0 {
  			l.state = S_1_G
  			l.succeeded = true
  			return nil
  		} else {
  			l.state = S_0_Y
  			return nil
  		}
  	case S_1_G:
  		if t0 {
  			l.state = S_1_G
  			l.succeeded = true
  			return nil
  		} else {
  			l.state = S_1_G
  			l.succeeded = true
  			return nil
  		}
  	default:
  		panic("invalid state")
  	}
  }
  
  type Monitor struct {
  	previous Global
  	PC       map[string]int
  	//vars     map[string][]string
  	vars        map[string]map[string]bool
  	ltlMonitor0 *LTLMonitor0
  }
  
  //func NewMonitor(vars map[string][]string) *Monitor {
  func NewMonitor(vars map[string]map[string]bool) *Monitor {
  	return &Monitor{
  		// previous is the empty Global
  		PC:          map[string]int{},
  		vars:        vars,
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
