Actions

  $ protocol print --parties P,C --project P --actions <<EOF
  > forall p in P
  >   forall c in C
  >     c.a = 1;
  >     c.x = 2;
  > 
  >     c->p: m;
  > 
  >     p->c: n;
  >     c.m = 1
  > EOF
  digraph G {
    0 [label="PReceiveM0\ntid: Pt0(c:C)\n{start}\nλ [(c:C)].\nc->self*: m"];
    1 [label="PSendN1\ntid: Pt0(c:C)\n{Pt0(c:C) = 0}\nλ [(c:C)].\n*self->c: n"];
    0 -> 1;
  }

  $ protocol print --parties P,C --project P --actions <<EOF
  > (forall p in P
  >    forall c in C
  >      c.a = 1;
  >      c.x = 2);
  > forall p in P
  >   forall c in C
  >     c.a = 3;
  >     c.x = 4
  > EOF
  digraph G {
  
  
  }

  $ protocol print --parties P,C --project C --actions <<EOF
  > (forall p in P
  >    forall c in C
  >      c.a = 1;
  >      c.x = 2);
  > forall p in P
  >   forall c in C
  >     c.a = 3;
  >     c.x = 4
  > EOF
  digraph G {
    0 [label="CChangeA0\ntid: Ct0(p:P)\n{start}\nc.a = 1;\nc.x = 2"];
    1 [label="CChangeA1\ntid: Ct1(p:P)\n{∀ p:P. Ct0(p:P) = 0}\nc.a = 3;\nc.x = 4"];
    0 -> 1;
  }

  $ protocol tla --parties P,C <<EOF
  > (forall p in P
  >    forall c in C
  >      c.a = 1;
  >      c.x = 2);
  > forall p in P
  >   forall c in C
  >     c.a = 3;
  >     c.x = 4
  > EOF
  -.tla
  -.cfg

  $ cat -- '-.tla'
  
  --------------------------------- MODULE - ---------------------------------
  
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
  
  CONSTANTS Ct0, Ct1
  
  CONSTANTS 
  
  \* Used by C
  
  VARIABLES a, x
  
  Cvars == <<a, x>>
  
  Pvars == <<>>
  
  vars == <<a, x, messages, pc>>
  
  threads == {Ct0, Ct1}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, <<Ct1, p2>>, <<Ct1, p1>>}
  
  Init ==
    /\ a = [i \in C |-> 0]
    /\ x = [i \in C |-> 0]
    /\ messages = [i \in {} |-> 0]
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> -1]]
  
  CChangeA0(self) ==
    /\ pc[self][<<Ct0, p>>] = -1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 0]]
    /\ 
      /\ a' = [a EXCEPT ![self] = 1]
      /\ x' = [x EXCEPT ![self] = 2]
    /\ UNCHANGED <<messages>>
  
  CChangeA1(self) ==
    /\ \A pi \in P : pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 1]]
    /\ 
      /\ a' = [a EXCEPT ![self] = 3]
      /\ x' = [x EXCEPT ![self] = 4]
    /\ UNCHANGED <<messages>>
  
  Next ==
    \/ \E self \in C : CChangeA0(self)
    \/ \E self \in C : CChangeA1(self)
  
  Spec == Init /\ [][Next]_vars
  
  ===============================================================================

  $ protocol tla --parties P,C simple.spec
  simple.tla
  simple.cfg

  $ cat simple.tla
  
  --------------------------------- MODULE simple ---------------------------------
  
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
  
  CONSTANTS Ct0, Cmain, Pt0
  
  CONSTANTS prepare, prepared, abort
  
  \* Used by C
  
  VARIABLES a, b
  
  Cvars == <<a, b>>
  
  Pvars == <<>>
  
  vars == <<a, b, messages, pc>>
  
  threads == {Ct0, Cmain, Pt0}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, Cmain, <<Pt0, c1>>}
  
  Init ==
    /\ a = [i \in C |-> 0]
    /\ b = [i \in C |-> 0]
    /\ messages = [i \in {} |-> 0]
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> -1]]
  
  CSendPrepare0(self, p) ==
    /\ pc[self][<<Ct0, p>>] = -1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 0]]
    /\ 
      /\ messages' = Send([mtype |-> prepare, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<a, b>>
  
  CReceivePrepared1(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 1]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = prepared
      /\ m.mdest = self
      /\ a' = [a EXCEPT ![self] = 1]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<b>>
  
  CReceiveAbort2(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 2]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
      /\ a' = [a EXCEPT ![self] = 2]
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<b>>
  
  CChangeB3(self) ==
    /\ \A pi \in P : 
      \/ pc[self][<<Ct0, p>>] = 1
      \/ pc[self][<<Ct0, p>>] = 2
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![Cmain] = 3]]
    /\ 
      /\ b' = [b EXCEPT ![self] = 3]
    /\ UNCHANGED <<a, messages>>
  
  PReceivePrepare4(self, c) ==
    /\ pc[self][<<Pt0, c>>] = -1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 4]]
    /\ \E m \in DOMAIN messages : 
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
      /\ messages' = Receive(m, messages)
    /\ UNCHANGED <<a, b>>
  
  PSendPrepared5(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 5]]
    /\ 
      /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<a, b>>
  
  PSendAbort6(self, c) ==
    /\ pc[self][<<Pt0, c>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt0, c>>] = 6]]
    /\ 
      /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<a, b>>
  
  Next ==
    \/ \E self \in C : \E p \in P : CSendPrepare0(self, p)
    \/ \E self \in C : \E p \in P : CReceivePrepared1(self, p)
    \/ \E self \in C : \E p \in P : CReceiveAbort2(self, p)
    \/ \E self \in C : CChangeB3(self)
    \/ \E self \in P : \E c \in C : PReceivePrepare4(self, c)
    \/ \E self \in P : \E c \in C : PSendPrepared5(self, c)
    \/ \E self \in P : \E c \in C : PSendAbort6(self, c)
  
  Spec == Init /\ [][Next]_vars
  
  ===============================================================================
