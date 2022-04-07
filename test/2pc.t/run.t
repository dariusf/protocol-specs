The classic two-phase commit protocol.

  $ protocol print 2pc.spec
  forall c in C
    (forall p in P
       c->p : prepare;
       (p->c : prepared
        \/
        p->c : abort;
        c.has_aborted = true));
    (has_aborted =>*
       (forall p in P
          c->p : abort;
          p->c : abort_ack;
          c.aborted = union(c.aborted, {p}))
     \/
     !(has_aborted) =>*
       (forall p in P
          c->p : commit;
          p->c : commit_ack;
          c.committed = union(c.committed, {p})))

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

  $ protocol print --types 2pc.spec
  forall (c : party C;global) in (C : map(party C, bool);global)
    (forall (p : party P;global) in (P : map(party P, bool);global)
       (c : party C;global)->(p : party P;global) : prepare;
       ((p : party P;global)->(c : party C;global) : prepared
        \/
        (p : party P;global)->(c : party C;global) : abort;
        (c.has_aborted : bool;C) = true));
    ((c.has_aborted : bool;C) =>*
       (forall (p : party P;global) in (P : map(party P, bool);global)
          (c : party C;global)->(p : party P;global) : abort;
          (p : party P;global)->(c : party C;global) : abort_ack;
          (c.aborted : map(party P, bool);C) = union((c.aborted : map(party P, bool);C), {(p : party P;global)}))
     \/
     !((c.has_aborted : bool;C)) =>*
       (forall (p : party P;global) in (P : map(party P, bool);global)
          (c : party C;global)->(p : party P;global) : commit;
          (p : party P;global)->(c : party C;global) : commit_ack;
          (c.committed : map(party P, bool);C) = union((c.committed : map(party P, bool);C), {(p : party P;global)})))

  $ protocol print 2pc.spec --project C
  (forall p in P
     ->p : prepare;
     (p-> : prepared
      \/
      p-> : abort;
      has_aborted = true));
  (has_aborted =>*
     (forall p in P
        ->p : abort;
        p-> : abort_ack;
        aborted = union(aborted, {p}))
   \/
   !(has_aborted) =>*
     (forall p in P
        ->p : commit;
        p-> : commit_ack;
        committed = union(committed, {p})))

  $ protocol print 2pc.spec --project P
  forall c in C
    c-> : prepare;
    (->c : prepared
     \/
     ->c : abort);
    (c-> : abort;
     ->c : abort_ack
     \/
     c-> : commit;
     ->c : commit_ack)

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && diff -uw 2pc1.spec 2pc2.spec

  $ protocol print 2pc-wait.spec > 2pc1-wait.spec && protocol print 2pc1-wait.spec | protocol print > 2pc2-wait.spec && diff -uw 2pc1-wait.spec 2pc2-wait.spec

  $ protocol print 2pc.spec --project P --actions
  digraph G {
    1 [label="PReceivePrepare1\n{start}\nc→ : prepare\n{Pt0(c:C) = 1}\n"];
    2 [label="PSendPrepared2\n{Pt0(c:C) = 1}\n→c : prepared\n{Pt0(c:C) = 2}\n"];
    3 [label="PSendAbort3\n{Pt0(c:C) = 1}\n→c : abort\n{Pt0(c:C) = 3}\n"];
    4 [label="PReceiveAbort4\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nc→ : abort\n{Pt0(c:C) = 4}\n"];
    5 [label="PSendAbortAck5\n{Pt0(c:C) = 4}\n→c : abort_ack\n{Pt0(c:C) = 5}\n"];
    6 [label="PReceiveCommit6\n{Any(Pt0(c:C) = 2, Pt0(c:C) = 3)}\nc→ : commit\n{Pt0(c:C) = 6}\n"];
    7 [label="PSendCommitAck7\n{Pt0(c:C) = 6}\n→c : commit_ack\n{Pt0(c:C) = 7}\n"];
    6 -> 7;
    4 -> 5;
    3 -> 6;
    3 -> 4;
    2 -> 6;
    2 -> 4;
    1 -> 3;
    1 -> 2;
  }

  $ protocol print 2pc.spec --project C --actions
  digraph G {
    1 [label="CSendPrepare1\n{start}\n→p : prepare\n{Ct0(p:P) = 1}\n"];
    2 [label="CReceivePrepared2\n{Ct0(p:P) = 1}\np→ : prepared\n{Ct0(p:P) = 2}\n"];
    3 [label="CReceiveAbort3\n{Ct0(p:P) = 1}\np→ : abort\n{Ct0(p:P) = 3}\n"];
    4 [label="CChangeHasAborted4\n{Ct0(p:P) = 3}\nhas_aborted = true\n{Ct0(p:P) = 4}\n"];
    5 [label="CSendAbort5\n{∀ p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 4)}\n→p : abort\n{Ct2(p:P) = 5}\n"];
    6 [label="CReceiveAbortAck6\n{Ct2(p:P) = 5}\np→ : abort_ack\n{Ct2(p:P) = 6}\n"];
    7 [label="CChangeAborted7\n{Ct2(p:P) = 6}\naborted = union(aborted, {p})\n{Ct2(p:P) = 7}\n"];
    8 [label="CSendCommit8\n{∀ p:P. Any(Ct0(p:P) = 2, Ct0(p:P) = 4)}\n→p : commit\n{Ct1(p:P) = 8}\n"];
    9 [label="CReceiveCommitAck9\n{Ct1(p:P) = 8}\np→ : commit_ack\n{Ct1(p:P) = 9}\n"];
    10 [label="CChangeCommitted10\n{Ct1(p:P) = 9}\ncommitted = union(committed, {p})\n{Ct1(p:P) = 10}\n"];
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

  $ protocol tla 2pc.spec
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
  
  CONSTANTS prepare, prepared, abort, abort_ack, commit, commit_ack
  
  Symmetry == (Permutations(C) \union Permutations(P))
  
  \* Used by C
  
  VARIABLES has_aborted, aborted, committed
  
  Cvars == <<has_aborted, aborted, committed>>
  
  Pvars == <<>>
  
  vars == <<has_aborted, aborted, committed, messages, pc>>
  
  threads == {Ct0, Ct2, Ct1, Pt3}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, <<Ct2, p2>>, <<Ct2, p1>>, <<Ct1, p2>>, <<Ct1, p1>>, <<Pt3, c1>>}
  
  Init ==
    /\ has_aborted = [i \in C |-> FALSE]
    /\ aborted = [i \in C |-> []]
    /\ committed = [i \in C |-> []]
    /\ messages = [i \in {} |-> 0]
    /\ history = <<>>
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> 0]]
  
  CSendPrepare1(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 1]]
    /\ history' = Append(<<"CSendPrepare1", p>>, history)
    /\ messages' = Send([mtype |-> prepare, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  CReceivePrepared2(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 2]]
    /\ history' = Append(<<"CReceivePrepared2", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepared
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  CReceiveAbort3(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 3]]
    /\ history' = Append(<<"CReceiveAbort3", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  CChangeHasAborted4(self) ==
    /\ pc[self][<<Ct0, p>>] = 3
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 4]]
    /\ history' = Append(<<"CChangeHasAborted4">>, history)
    /\ has_aborted' = [has_aborted EXCEPT ![self] = TRUE]
    /\ UNCHANGED <<aborted, committed, messages>>
  
  CSendAbort5(self, p) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 5]]
    /\ history' = Append(<<"CSendAbort5", p>>, history)
    /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  CReceiveAbortAck6(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 5
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 6]]
    /\ history' = Append(<<"CReceiveAbortAck6", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort_ack
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  CChangeAborted7(self, p) ==
    /\ pc[self][<<Ct2, p>>] = 6
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct2, p>>] = 7]]
    /\ history' = Append(<<"CChangeAborted7", p>>, history)
    /\ aborted' = [aborted EXCEPT ![self] = (aborted[self] \union {p})]
    /\ UNCHANGED <<has_aborted, committed, messages>>
  
  CSendCommit8(self, p) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 2
      \/ pc[self][<<Ct0, pi>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 8]]
    /\ history' = Append(<<"CSendCommit8", p>>, history)
    /\ messages' = Send([mtype |-> commit, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  CReceiveCommitAck9(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 8
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 9]]
    /\ history' = Append(<<"CReceiveCommitAck9", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = commit_ack
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  CChangeCommitted10(self, p) ==
    /\ pc[self][<<Ct1, p>>] = 9
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 10]]
    /\ history' = Append(<<"CChangeCommitted10", p>>, history)
    /\ committed' = [committed EXCEPT ![self] = (committed[self] \union {p})]
    /\ UNCHANGED <<has_aborted, aborted, messages>>
  
  PReceivePrepare11(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 11]]
    /\ history' = Append(<<"PReceivePrepare11", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  PSendPrepared12(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 11
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 12]]
    /\ history' = Append(<<"PSendPrepared12", c>>, history)
    /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  PSendAbort13(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 11
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 13]]
    /\ history' = Append(<<"PSendAbort13", c>>, history)
    /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  PReceiveAbort14(self, c) ==
    /\
      \/ pc[self][<<Pt3, c>>] = 12
      \/ pc[self][<<Pt3, c>>] = 13
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 14]]
    /\ history' = Append(<<"PReceiveAbort14", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  PSendAbortAck15(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 14
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 15]]
    /\ history' = Append(<<"PSendAbortAck15", c>>, history)
    /\ messages' = Send([mtype |-> abort_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  PReceiveCommit16(self, c) ==
    /\
      \/ pc[self][<<Pt3, c>>] = 12
      \/ pc[self][<<Pt3, c>>] = 13
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 16]]
    /\ history' = Append(<<"PReceiveCommit16", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = commit
      /\ m.mdest = self
    /\ UNCHANGED <<has_aborted, aborted, committed, messages>>
  
  PSendCommitAck17(self, c) ==
    /\ pc[self][<<Pt3, c>>] = 16
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, c>>] = 17]]
    /\ history' = Append(<<"PSendCommitAck17", c>>, history)
    /\ messages' = Send([mtype |-> commit_ack, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<has_aborted, aborted, committed>>
  
  Next ==
    \/ \E self \in C : \E p \in P : CSendPrepare1(self, p)
    \/ \E self \in C : \E p \in P : CReceivePrepared2(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbort3(self, p)
    \/ \E self \in C : CChangeHasAborted4(self)
    \/ \E self \in C : \E p \in P : CSendAbort5(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbortAck6(self, p)
    \/ \E self \in C : \E p \in P : CChangeAborted7(self, p)
    \/ \E self \in C : \E p \in P : CSendCommit8(self, p)
    \/ \E self \in C : \E p \in P : CReceiveCommitAck9(self, p)
    \/ \E self \in C : \E p \in P : CChangeCommitted10(self, p)
    \/ \E self \in P : \E c \in C : PReceivePrepare11(self, c)
    \/ \E self \in P : \E c \in C : PSendPrepared12(self, c)
    \/ \E self \in P : \E c \in C : PSendAbort13(self, c)
    \/ \E self \in P : \E c \in C : PReceiveAbort14(self, c)
    \/ \E self \in P : \E c \in C : PSendAbortAck15(self, c)
    \/ \E self \in P : \E c \in C : PReceiveCommit16(self, c)
    \/ \E self \in P : \E c \in C : PSendCommitAck17(self, c)
  
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
    abort = abort
    abort_ack = abort_ack
    commit = commit
    commit_ack = commit_ack
    Ct0 = Ct0
    Ct2 = Ct2
    Ct1 = Ct1
    Pt3 = Pt3
  SYMMETRY Symmetry
  SPECIFICATION Spec
  VIEW vars
  \* INVARIANT Inv


  $ protocol monitor 2pc.spec
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
  	Aborted    map[string]bool
  	Committed  map[string]bool
  }
  
  type Action int
  
  const (
  	CSendPrepare1 Action = iota
  	CReceivePrepared2
  	CReceiveAbort3
  	CChangeHasAborted4
  	CSendAbort5
  	CReceiveAbortAck6
  	CChangeAborted7
  	CSendCommit8
  	CReceiveCommitAck9
  	CChangeCommitted10
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
  	case CSendAbort5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(g.HasAborted) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CSendAbort5", params)
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 4 })) {
  			return fmt.Errorf("control precondition of CSendAbort5 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendAbort5", params: params})
  		return nil
  	case CReceiveAbortAck6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct2_"+(params[0] /* p : P */)] == 5) {
  			return fmt.Errorf("control precondition of CReceiveAbortAck6 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveAbortAck6", params: params})
  		return nil
  	case CChangeAborted7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct2_"+(params[0] /* p : P */)] == 6) {
  			return fmt.Errorf("control precondition of CChangeAborted7 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeAborted7", params: params})
  		return nil
  	case CSendCommit8:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		if g != nil && !(!(g.HasAborted)) {
  			return fmt.Errorf("logical precondition of %s, %v violated", "CSendCommit8", params)
  		}
  		if !(allSet(m.vars["P"], func(p string) bool { return m.PC["Ct0_"+(p)] == 2 || m.PC["Ct0_"+(p)] == 4 })) {
  			return fmt.Errorf("control precondition of CSendCommit8 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CSendCommit8", params: params})
  		return nil
  	case CReceiveCommitAck9:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct1_"+(params[0] /* p : P */)] == 8) {
  			return fmt.Errorf("control precondition of CReceiveCommitAck9 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CReceiveCommitAck9", params: params})
  		return nil
  	case CChangeCommitted10:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		// no preconditions
  		if !(m.PC["Ct1_"+(params[0] /* p : P */)] == 9) {
  			return fmt.Errorf("control precondition of CChangeCommitted10 %v violated", params)
  		}
  		m.Log = append(m.Log, entry{action: "CChangeCommitted10", params: params})
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
  	case CSendAbort5:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 5
  	case CReceiveAbortAck6:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 6
  	case CChangeAborted7:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct2_"+(params[0] /* p : P */)] = 7
  	case CSendCommit8:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 8
  	case CReceiveCommitAck9:
  		if len(params) != 1 {
  			return errors.New("expected 1 params")
  		}
  		m.PC["Ct1_"+(params[0] /* p : P */)] = 9
  	case CChangeCommitted10:
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
