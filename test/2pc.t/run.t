The classic two-phase commit protocol.

  $ protocol print 2pc.spec
  forall c in C
    (forall p in P
       c->p : prepare;
       (p->c : prepared
        \/
        p->c : abort;
        c.has_aborted = true));
    (!(has_aborted) =>
       (forall p in P
          c->p : commit;
          p->c : commit_ack(p=p);
          committed = union(committed, {p}))
     \/
     has_aborted =>
       (forall p in P
          c->p : abort;
          p->c : abort_ack(p=p);
          aborted = union(aborted, {p})))

  $ protocol print 2pc-wait.spec
  forall c in C
    forall p in P
      c->p : prepare;
      (p->c : prepared;
       responded = union(responded, {p})
       \/
       p->c : abort;
       aborted = union(aborted, {p}))
  ||
  responded == P =>*
    (forall p in P
       c->p : commit;
       p->c : commit_ack)
  \/
  aborted != {} =>*
    (forall p in P
       c->p : abort;
       p->c : abort_ack)

  $ protocol print --parties P,C --types 2pc.spec
  forall (c : party C;global) in (C : {party C};global)
    (forall (p : party P;global) in (P : {party P};global)
       (c : party C;global)->(p : party P;global) : prepare;
       ((p : party P;global)->(c : party C;global) : prepared
        \/
        (p : party P;global)->(c : party C;global) : abort;
        (c.has_aborted : bool;C) = true));
    (!((c.has_aborted : bool;C)) =>
       (forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global) : commit;
          (p : party P;global)->(c : party C;global) : commit_ack((p : party P;C)=(p : party P;global));
          (c.committed : {party P};C) = union((c.committed : {party P};C), {(p : party P;C)}))
     \/
     (c.has_aborted : bool;C) =>
       (forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global) : abort;
          (p : party P;global)->(c : party C;global) : abort_ack((p : party P;C)=(p : party P;global));
          (c.aborted : {party P};C) = union((c.aborted : {party P};C), {(p : party P;C)})))

  $ protocol print 2pc.spec --parties C,P --project C
  (forall p in P
     ->p : prepare;
     (p-> : prepared
      \/
      p-> : abort;
      has_aborted = true));
  (!(has_aborted) =>
     (forall p in P
        ->p : commit;
        p-> : commit_ack(p);
        committed = union(committed, {p}))
   \/
   has_aborted =>
     (forall p in P
        ->p : abort;
        p-> : abort_ack(p);
        aborted = union(aborted, {p})))

  $ protocol print 2pc.spec --parties C,P --project P
  forall c in C
    c-> : prepare;
    (->c : prepared
     \/
     ->c : abort);
    (c-> : commit;
     ->c : commit_ack(p=self)
     \/
     c-> : abort;
     ->c : abort_ack(p=self))

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && diff -uw 2pc1.spec 2pc2.spec

  $ protocol print 2pc-wait.spec > 2pc1-wait.spec && protocol print 2pc1-wait.spec | protocol print > 2pc2-wait.spec && diff -uw 2pc1-wait.spec 2pc2-wait.spec

  $ protocol print 2pc.spec --parties C,P --project P --actions
  digraph G {
    1 [label="PReceivePrepare1\n{start}\nc??? : prepare\n{Pt0(c:C) = 1}\n"];
    2 [label="PSendPrepared2\n{Pt0(c:C) = 1}\n???c : prepared\n{Pt0(c:C) = 2}\n"];
    3 [label="PSendAbort3\n{Pt0(c:C) = 1}\n???c : abort\n{Pt0(c:C) = 3}\n"];
    4 [label="PReceiveCommit4\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nc??? : commit\n{Pt0(c:C) = 4}\n"];
    5 [label="PSendCommitAck5\n{Pt0(c:C) = 4}\n???c : commit_ack(p=self)\n{Pt0(c:C) = 5}\n"];
    6 [label="PReceiveAbort6\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nc??? : abort\n{Pt0(c:C) = 6}\n"];
    7 [label="PSendAbortAck7\n{Pt0(c:C) = 6}\n???c : abort_ack(p=self)\n{Pt0(c:C) = 7}\n"];
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
    1 [label="CSendPrepare1\n{start}\n???p : prepare\n{Ct0(p:P) = 1}\n"];
    2 [label="CReceivePrepared2\n{Ct0(p:P) = 1}\np??? : prepared\n{Ct0(p:P) = 2}\n"];
    3 [label="CReceiveAbort3\n{Ct0(p:P) = 1}\np??? : abort;\nhas_aborted = true\n{Ct0(p:P) = 3}\n"];
    4 [label="CSendCommit4\n{??? p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 3)}\n???p : commit\n{Ct2(p:P) = 4}\n"];
    5 [label="CReceiveCommitAck5\n{Ct2(p:P) = 4}\np??? : commit_ack(p);\ncommitted = union(committed, {p})\n{Ct2(p:P) = 5}\n"];
    6 [label="CSendAbort6\n{??? p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 3)}\n???p : abort\n{Ct1(p:P) = 6}\n"];
    7 [label="CReceiveAbortAck7\n{Ct1(p:P) = 6}\np??? : abort_ack(p);\naborted = union(aborted, {p})\n{Ct1(p:P) = 7}\n"];
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
  
  VARIABLES has_aborted, committed, aborted
  
  Cvars == <<has_aborted, committed, aborted>>
  
  Pvars == <<>>
  
  vars == <<has_aborted, committed, aborted, messages, pc>>
  
  threads == {Ct0, Ct2, Ct1, Pt0}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, <<Ct2, p2>>, <<Ct2, p1>>, <<Ct1, p2>>, <<Ct1, p1>>, <<Pt0, c1>>}
  
  Init ==
    /\ has_aborted = [i \in C |-> FALSE]
    /\ committed = [i \in C |-> {}]
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
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  CReceivePrepared2(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 2]]
    /\ history' = Append(<<"CReceivePrepared2", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepared
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  CReceiveAbort3(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 3]]
    /\ history' = Append(<<"CReceiveAbort3", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ has_aborted' = [has_aborted EXCEPT ![self] = TRUE]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<committed, aborted>>
  
  CSendCommit4(self, p) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 4]]
    /\ history' = Append(<<"CSendCommit4", p>>, history)
    /\
      /\ messages' = Send([mtype |-> commit, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  CReceiveCommitAck5(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 5]]
    /\ history' = Append(<<"CReceiveCommitAck5", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = commit_ack
      /\ m.mdest = self
      /\ LET
          p == m.p
           IN
  
        /\ committed' = [committed EXCEPT ![self] = (committed[self] \union {p})]
        /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<has_aborted, aborted>>
  
  CSendAbort6(self, p) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 6]]
    /\ history' = Append(<<"CSendAbort6", p>>, history)
    /\
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  CReceiveAbortAck7(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 6
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 7]]
    /\ history' = Append(<<"CReceiveAbortAck7", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort_ack
      /\ m.mdest = self
      /\ LET
          p == m.p
           IN
  
        /\ aborted' = [aborted EXCEPT ![self] = (aborted[self] \union {p})]
        /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<has_aborted, committed>>
  
  PReceivePrepare8(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 8]]
    /\ history' = Append(<<"PReceivePrepare8", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PSendPrepared9(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 8
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 9]]
    /\ history' = Append(<<"PSendPrepared9", c>>, history)
    /\
      /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PSendAbort10(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 8
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 10]]
    /\ history' = Append(<<"PSendAbort10", c>>, history)
    /\
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
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
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PSendCommitAck12(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 11
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 12]]
    /\ history' = Append(<<"PSendCommitAck12", c>>, history)
    /\
      /\ messages' = Send([p |-> self, mtype |-> commit_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
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
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PSendAbortAck14(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 13
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 14]]
    /\ history' = Append(<<"PSendAbortAck14", c>>, history)
    /\
      /\ messages' = Send([p |-> self, mtype |-> abort_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
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
  package rvc
  
  import (
  	"errors"
  	"fmt"
  	"reflect"
  	"sync"
  	"time"
  )
  
  type Global struct {
  	HasAborted bool
  	Committed  map[string]bool
  	Aborted    map[string]bool
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
  			return fmt.Errorf("control precondition of CSendPrepare1 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendPrepare1", params: params})
  		return nil
  	case CReceivePrepared2:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct0_"+(params[0] /* p : P */)] == 1) {
  			return fmt.Errorf("control precondition of CReceivePrepared2 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceivePrepared2", params: params})
  		return nil
  	case CReceiveAbort3:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct0_"+(params[0] /* p : P */)] == 1) {
  			return fmt.Errorf("control precondition of CReceiveAbort3 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveAbort3", params: params})
  		return nil
  	case CSendCommit4:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(!(g.HasAborted)) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CSendCommit4", params)
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 3 })) {
  			return fmt.Errorf("control precondition of CSendCommit4 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendCommit4", params: params})
  		return nil
  	case CReceiveCommitAck5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct2_"+(params[0] /* p : P */)] == 4) {
  			return fmt.Errorf("control precondition of CReceiveCommitAck5 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveCommitAck5", params: params})
  		return nil
  	case CSendAbort6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(g.HasAborted) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CSendAbort6", params)
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 3 })) {
  			return fmt.Errorf("control precondition of CSendAbort6 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendAbort6", params: params})
  		return nil
  	case CReceiveAbortAck7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct1_"+(params[0] /* p : P */)] == 6) {
  			return fmt.Errorf("control precondition of CReceiveAbortAck7 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveAbortAck7", params: params})
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
  	return reflect.DeepEqual((len(g.Committed) + len(g.Aborted)), len(l.vars["P"]))
  }
  func (l *LTLMonitor0) t1(g Global) bool {
  	return (reflect.DeepEqual(g.Committed, map[string]bool{}) || reflect.DeepEqual(g.Aborted, map[string]bool{}))
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
  	t1 := l.t1(g)
  
  	// note the true ones, take that transition
  	switch l.state {
  	case S_0_R:
  		if t0 {
  			if t1 {
  				l.state = S_0_R
  				l.failed = true
  				return errors.New("property falsified")
  			} else {
  				l.state = S_0_R
  				l.failed = true
  				return errors.New("property falsified")
  			}
  		} else {
  			if t1 {
  				l.state = S_0_R
  				l.failed = true
  				return errors.New("property falsified")
  			} else {
  				l.state = S_0_R
  				l.failed = true
  				return errors.New("property falsified")
  			}
  		}
  	case S_1_Y:
  		if t0 {
  			if t1 {
  				l.state = S_1_Y
  				return nil
  			} else {
  				l.state = S_0_R
  				l.failed = true
  				return errors.New("property falsified")
  			}
  		} else {
  			if t1 {
  				l.state = S_1_Y
  				return nil
  			} else {
  				l.state = S_1_Y
  				return nil
  			}
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
