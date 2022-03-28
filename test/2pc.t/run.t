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
    1 [label="PReceivePrepare1\n{start}\nc→ : prepare\n{Pt0(c:C) = 1}\n"];
    2 [label="PSendPrepared2\n{Pt0(c:C) = 1}\n→c : prepared\n{Pt0(c:C) = 2}\n"];
    3 [label="PSendAbort3\n{Pt0(c:C) = 1}\n→c : abort\n{Pt0(c:C) = 3}\n"];
    4 [label="PReceiveCommit4\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nc→ : commit\n{Pt0(c:C) = 4}\n"];
    5 [label="PSendCommitAck5\n{Pt0(c:C) = 4}\n→c : commit_ack(p=self)\n{Pt0(c:C) = 5}\n"];
    6 [label="PReceiveAbort6\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nc→ : abort\n{Pt0(c:C) = 6}\n"];
    7 [label="PSendAbortAck7\n{Pt0(c:C) = 6}\n→c : abort_ack(p=self)\n{Pt0(c:C) = 7}\n"];
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
    1 [label="CSendPrepare1\n{start}\n→p : prepare\n{Ct0(p:P) = 1}\n"];
    2 [label="CReceivePrepared2\n{Ct0(p:P) = 1}\np→ : prepared\n{Ct0(p:P) = 2}\n"];
    3 [label="CReceiveAbort3\n{Ct0(p:P) = 1}\np→ : abort\n{Ct0(p:P) = 3}\n"];
    4 [label="CChangeHasAborted4\n{Ct0(p:P) = 3}\nhas_aborted = true\n{Ct0(p:P) = 4}\n"];
    5 [label="CSendCommit5\n{∀ p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 4)}\n→p : commit\n{Ct2(p:P) = 5}\n"];
    6 [label="CReceiveCommitAck6\n{Ct2(p:P) = 5}\np→ : commit_ack(p)\n{Ct2(p:P) = 6}\n"];
    7 [label="CChangeCommitted7\n{Ct2(p:P) = 6}\ncommitted = union(committed, {p})\n{Ct2(p:P) = 7}\n"];
    8 [label="CSendAbort8\n{∀ p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 4)}\n→p : abort\n{Ct1(p:P) = 8}\n"];
    9 [label="CReceiveAbortAck9\n{Ct1(p:P) = 8}\np→ : abort_ack(p)\n{Ct1(p:P) = 9}\n"];
    10 [label="CChangeAborted10\n{Ct1(p:P) = 9}\naborted = union(aborted, {p})\n{Ct1(p:P) = 10}\n"];
    9 -> 10;
    8 -> 9;
    6 -> 7;
    5 -> 6;
    4 -> 8;
    4 -> 5;
    3 -> 4;
    2 -> 8;
    2 -> 5;
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
  
  CONSTANTS Ct0, Ct2, Ct1, Pt3
  
  CONSTANTS prepare, prepared, commit, commit_ack, abort, abort_ack
  
  Symmetry == (Permutations(C) \union Permutations(P))
  
  \* Used by C
  
  VARIABLES has_aborted, committed, aborted
  
  Cvars == <<has_aborted, committed, aborted>>
  
  Pvars == <<>>
  
  vars == <<has_aborted, committed, aborted, messages, pc>>
  
  threads == {Ct0, Ct2, Ct1, Pt3}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, <<Ct2, p2>>, <<Ct2, p1>>, <<Ct1, p2>>, <<Ct1, p1>>, <<Pt3, c1>>}
  
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
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  CReceiveAbort3(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 3]]
    /\ history' = Append(<<"CReceiveAbort3", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  CChangeHasAborted4(self) ==
    /\ pc[self][<<Ct0, p>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 4]]
    /\ history' = Append(<<"CChangeHasAborted4">>, history)
    /\ has_aborted' = [has_aborted EXCEPT ![self] = TRUE]
    /\ UNCHANGED <<committed, aborted, messages>>
  
  CSendCommit5(self, p) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 5]]
    /\ history' = Append(<<"CSendCommit5", p>>, history)
    /\ messages' = Send([mtype |-> commit, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  CReceiveCommitAck6(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 5
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 6]]
    /\ history' = Append(<<"CReceiveCommitAck6", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = commit_ack
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  CChangeCommitted7(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 6
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 7]]
    /\ history' = Append(<<"CChangeCommitted7", p>>, history)
    /\ committed' = [committed EXCEPT ![self] = (committed[self] \union {p})]
    /\ UNCHANGED <<has_aborted, aborted, messages>>
  
  CSendAbort8(self, p) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 8]]
    /\ history' = Append(<<"CSendAbort8", p>>, history)
    /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  CReceiveAbortAck9(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 8
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 9]]
    /\ history' = Append(<<"CReceiveAbortAck9", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort_ack
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  CChangeAborted10(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 9
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 10]]
    /\ history' = Append(<<"CChangeAborted10", p>>, history)
    /\ aborted' = [aborted EXCEPT ![self] = (aborted[self] \union {p})]
    /\ UNCHANGED <<has_aborted, committed, messages>>
  
  PReceivePrepare11(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 11]]
    /\ history' = Append(<<"PReceivePrepare11", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  PSendPrepared12(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 11
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 12]]
    /\ history' = Append(<<"PSendPrepared12", c>>, history)
    /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PSendAbort13(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 11
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 13]]
    /\ history' = Append(<<"PSendAbort13", c>>, history)
    /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PReceiveCommit14(self, c) ==
    /\
      \/ pc[self][<<Pt3, c>>] = 12
      \/ pc[self][<<Pt3, c>>] = 13
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 14]]
    /\ history' = Append(<<"PReceiveCommit14", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = commit
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  PSendCommitAck15(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 14
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 15]]
    /\ history' = Append(<<"PSendCommitAck15", c>>, history)
    /\ messages' = Send([p |-> self, mtype |-> commit_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  PReceiveAbort16(self, c) ==
    /\
      \/ pc[self][<<Pt3, c>>] = 12
      \/ pc[self][<<Pt3, c>>] = 13
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 16]]
    /\ history' = Append(<<"PReceiveAbort16", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, committed, aborted, messages>>
  
  PSendAbortAck17(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 16
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 17]]
    /\ history' = Append(<<"PSendAbortAck17", c>>, history)
    /\ messages' = Send([p |-> self, mtype |-> abort_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, committed, aborted>>
  
  Next ==
    \/ \E self \in C : \E p \in P : CSendPrepare1(self, p)
    \/ \E self \in C : \E p \in P : CReceivePrepared2(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbort3(self, p)
    \/ \E self \in C : CChangeHasAborted4(self)
    \/ \E self \in C : \E p \in P : CSendCommit5(self, p)
    \/ \E self \in C : \E p \in P : CReceiveCommitAck6(self, p)
    \/ \E self \in C : \E p \in P : CChangeCommitted7(self, p)
    \/ \E self \in C : \E p \in P : CSendAbort8(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbortAck9(self, p)
    \/ \E self \in C : \E p \in P : CChangeAborted10(self, p)
    \/ \E self \in P : \E c \in C : PReceivePrepare11(self, c)
    \/ \E self \in P : \E c \in C : PSendPrepared12(self, c)
    \/ \E self \in P : \E c \in C : PSendAbort13(self, c)
    \/ \E self \in P : \E c \in C : PReceiveCommit14(self, c)
    \/ \E self \in P : \E c \in C : PSendCommitAck15(self, c)
    \/ \E self \in P : \E c \in C : PReceiveAbort16(self, c)
    \/ \E self \in P : \E c \in C : PSendAbortAck17(self, c)
  
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
    Pt3 = Pt3
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
  	CChangeHasAborted4
  	CSendCommit5
  	CReceiveCommitAck6
  	CChangeCommitted7
  	CSendAbort8
  	CReceiveAbortAck9
  	CChangeAborted10
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
  	case CChangeHasAborted4:
  
  		// no preconditions
  		if !(m.PC["Ct0_"+(params[0] /* p : P */)] == 3) {
  			return fmt.Errorf("control precondition of CChangeHasAborted4 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeHasAborted4", params: params})
  		return nil
  	case CSendCommit5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(!(g.HasAborted)) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CSendCommit5", params)
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 4 })) {
  			return fmt.Errorf("control precondition of CSendCommit5 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendCommit5", params: params})
  		return nil
  	case CReceiveCommitAck6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct2_"+(params[0] /* p : P */)] == 5) {
  			return fmt.Errorf("control precondition of CReceiveCommitAck6 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveCommitAck6", params: params})
  		return nil
  	case CChangeCommitted7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct2_"+(params[0] /* p : P */)] == 6) {
  			return fmt.Errorf("control precondition of CChangeCommitted7 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeCommitted7", params: params})
  		return nil
  	case CSendAbort8:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(g.HasAborted) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CSendAbort8", params)
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 4 })) {
  			return fmt.Errorf("control precondition of CSendAbort8 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendAbort8", params: params})
  		return nil
  	case CReceiveAbortAck9:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct1_"+(params[0] /* p : P */)] == 8) {
  			return fmt.Errorf("control precondition of CReceiveAbortAck9 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveAbortAck9", params: params})
  		return nil
  	case CChangeAborted10:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct1_"+(params[0] /* p : P */)] == 9) {
  			return fmt.Errorf("control precondition of CChangeAborted10 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeAborted10", params: params})
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
  	case CChangeHasAborted4:
  
  		m.PC["Ct0_"+(params[0] /* p : P */)] = 4
  	case CSendCommit5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 5
  	case CReceiveCommitAck6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 6
  	case CChangeCommitted7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 7
  	case CSendAbort8:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 8
  	case CReceiveAbortAck9:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 9
  	case CChangeAborted10:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 10
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
