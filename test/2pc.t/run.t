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
     *self->p: prepare;
     (p->self*: prepared;
      responded = union(responded, {p})
      \/
      p->self*: abort;
      aborted = union(aborted, {p})));
  (aborted == {} =>
     (forall p in P
        *self->p: commit;
        p->self*: commit_ack)
   \/
   aborted != {} =>
     (forall p in P
        *self->p: abort;
        p->self*: abort_ack))

  $ protocol print 2pc.spec --parties C,P --project P
  forall c in C
    c->self*: prepare;
    (*self->c: prepared
     \/
     *self->c: abort);
    (c->self*: commit;
     *self->c: commit_ack
     \/
     c->self*: abort;
     *self->c: abort_ack)

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && git diff --no-index 2pc1.spec 2pc2.spec

  $ protocol print 2pc-wait.spec > 2pc1-wait.spec && protocol print 2pc1-wait.spec | protocol print > 2pc2-wait.spec && git diff --no-index 2pc1-wait.spec 2pc2-wait.spec

  $ protocol print 2pc.spec --parties C,P --project P --actions
  digraph G {
    0 [label="λ c:C.\nc->self*: prepare"];
    1 [label="λ c:C.\n*self->c: prepared"];
    2 [label="λ c:C.\n*self->c: abort"];
    3 [label="λ c:C.\nc->self*: commit"];
    4 [label="λ c:C.\n*self->c: commit_ack"];
    5 [label="λ c:C.\nc->self*: abort"];
    6 [label="λ c:C.\n*self->c: abort_ack"];
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
    0 [label="λ p:P.\n*self->p: prepare"];
    1 [label="λ p:P.\np->self*: prepared;\nresponded = union(responded, {p})"];
    2 [label="λ p:P.\np->self*: abort;\naborted = union(aborted, {p})"];
    3 [label="{aborted == {}}\nλ p:P.\n*self->p: commit"];
    4 [label="{aborted == {}}\nλ p:P.\np->self*: commit_ack"];
    5 [label="{aborted != {}}\nλ p:P.\n*self->p: abort"];
    6 [label="{aborted != {}}\nλ p:P.\np->self*: abort_ack"];
    5 -> 6;
    3 -> 4;
    2 -> 5;
    2 -> 3;
    1 -> 5;
    1 -> 3;
    0 -> 2;
    0 -> 1;
  }

  $ protocol tla 2pc.spec --parties C,P --project C
  
  --------------------------------- MODULE spec ---------------------------------
  
  EXTENDS Naturals, FiniteSets, Sequences
  
  VARIABLE messages
  
  Send(m, msgs) ==
      IF m \in DOMAIN msgs THEN
          [msgs EXCEPT ![m] = msgs[m] + 1]
      ELSE
          msgs @ (m :> 1)
  
  Receive(m, msgs) ==
      IF m \in DOMAIN msgs THEN
          [msgs EXCEPT ![m] = msgs[m] - 1]
      ELSE
          msgs
  
  VARIABLE pc
  
  
  CONSTANT C
  
  CONSTANT P
  
  Cvars == <<responded, aborted>>
  
  Pvars == <<>>
  
  vars == <<responded, aborted, messages>>
  
  \* Used by C
  
  VARIABLES responded aborted
  
  Init ==
    /\ responded = [i \in C |-> {}]
    /\ aborted = [i \in C |-> {}]
  
  CSendPrepare0(self, p) ==
    /\ pc' = [pc EXCEPT ![self] = 0]
    /\ 
      /\ messages' = Send([mtype |-> prepare, msrc |-> self, mdest |-> p])
    /\ UNCHANGED <<responded, aborted, messages>>
  
  CReceivePrepared1(self, p) ==
    /\ pc = 0
    /\ pc' = [pc EXCEPT ![self] = 1]
    /\ \E m \in messages : 
      /\ m.mtype = prepared
      /\ m.mdest = self
      /\ responded' = [responded EXCEPT ![self] = (responded[self] \union {p})]
      /\ messages' = Receive(m)
    /\ UNCHANGED <<aborted>>
  
  CReceiveAbort2(self, p) ==
    /\ pc = 0
    /\ pc' = [pc EXCEPT ![self] = 2]
    /\ \E m \in messages : 
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ aborted' = [aborted EXCEPT ![self] = (aborted[self] \union {p})]
      /\ messages' = Receive(m)
    /\ UNCHANGED <<responded>>
  
  CSendCommit3(self, p) ==
    /\ 
      \/ pc = 2
      \/ pc = 1
    /\ pc' = [pc EXCEPT ![self] = 3]
    /\ 
      /\ messages' = Send([mtype |-> commit, msrc |-> self, mdest |-> p])
    /\ UNCHANGED <<responded, aborted, messages>>
  
  CReceiveCommitAck4(self, p) ==
    /\ pc = 3
    /\ pc' = [pc EXCEPT ![self] = 4]
    /\ \E m \in messages : 
      /\ m.mtype = commit_ack
      /\ m.mdest = self
      /\ messages' = Receive(m)
    /\ UNCHANGED <<responded, aborted>>
  
  CSendAbort5(self, p) ==
    /\ 
      \/ pc = 2
      \/ pc = 1
    /\ pc' = [pc EXCEPT ![self] = 5]
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> p])
    /\ UNCHANGED <<responded, aborted, messages>>
  
  CReceiveAbortAck6(self, p) ==
    /\ pc = 5
    /\ pc' = [pc EXCEPT ![self] = 6]
    /\ \E m \in messages : 
      /\ m.mtype = abort_ack
      /\ m.mdest = self
      /\ messages' = Receive(m)
    /\ UNCHANGED <<responded, aborted>>
  
  PReceivePrepare7(self, c) ==
    /\ pc' = [pc EXCEPT ![self] = 7]
    /\ \E m \in messages : 
      /\ m.mtype = prepare
      /\ m.mdest = self
      /\ messages' = Receive(m)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendPrepared8(self, c) ==
    /\ pc = 7
    /\ pc' = [pc EXCEPT ![self] = 8]
    /\ 
      /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c])
    /\ UNCHANGED <<responded, aborted, messages>>
  
  PSendAbort9(self, c) ==
    /\ pc = 7
    /\ pc' = [pc EXCEPT ![self] = 9]
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c])
    /\ UNCHANGED <<responded, aborted, messages>>
  
  PReceiveCommit10(self, c) ==
    /\ 
      \/ pc = 9
      \/ pc = 8
    /\ pc' = [pc EXCEPT ![self] = 10]
    /\ \E m \in messages : 
      /\ m.mtype = commit
      /\ m.mdest = self
      /\ messages' = Receive(m)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendCommitAck11(self, c) ==
    /\ pc = 10
    /\ pc' = [pc EXCEPT ![self] = 11]
    /\ 
      /\ messages' = Send([mtype |-> commit_ack, msrc |-> self, mdest |-> c])
    /\ UNCHANGED <<responded, aborted, messages>>
  
  PReceiveAbort12(self, c) ==
    /\ 
      \/ pc = 9
      \/ pc = 8
    /\ pc' = [pc EXCEPT ![self] = 12]
    /\ \E m \in messages : 
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ messages' = Receive(m)
    /\ UNCHANGED <<responded, aborted>>
  
  PSendAbortAck13(self, c) ==
    /\ pc = 12
    /\ pc' = [pc EXCEPT ![self] = 13]
    /\ 
      /\ messages' = Send([mtype |-> abort_ack, msrc |-> self, mdest |-> c])
    /\ UNCHANGED <<responded, aborted, messages>>
  
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
  
