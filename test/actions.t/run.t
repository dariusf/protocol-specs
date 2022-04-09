Actions

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > forall p in P
  >     p.a = 1
  > EOF
  digraph G {
    1 [label="PChangeA1\n{start(Pmain)}\na = 1\n{Pmain = 1}\n"];
  }

Default grain

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > forall p in P
  >     p.a = 1;
  >     p.b = 2
  > EOF
  digraph G {
    1 [label="PChangeA1\n{start(Pmain)}\na = 1;\nb = 2\n{Pmain = 2}\n"];
  }

Fuse tail

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   forall c in C
  >     p->c: m;
  >     p.b = 2;
  >     p.a = 1
  > EOF
  digraph G {
    1 [label="PSendM1\n{start(Pt0(c:C))}\nc! m\n{Pt0(c:C) = 1}\n"];
    2 [label="PChangeB2\n{Pt0(c:C) = 1}\nb = 2;\na = 1\n{Pt0(c:C) = 3}\n"];
    1 -> 2;
  }

Fuse head

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   forall c in C
  >     p.b = 2;
  >     p.a = 1;
  >     p->c: m
  > EOF
  digraph G {
    1 [label="PChangeB1\n{start(Pt0(c:C))}\nb = 2;\na = 1\n{Pt0(c:C) = 2}\n"];
    3 [label="PSendM3\n{Pt0(c:C) = 2}\nc! m\n{Pt0(c:C) = 3}\n"];
    1 -> 3;
  }

Communication grain (P)

  $ protocol print --project P --actions --grain communication <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   forall c in C
  >     p.a = 1;
  >     p->c: m;
  >     c.b = 1;
  >     c->p: m
  > EOF
  digraph G {
    1 [label="PChangeA1\n{start(Pt0(c:C))}\na = 1;\nc! m\n{Pt0(c:C) = 2}\n"];
    3 [label="PReceiveM3\n{Pt0(c:C) = 2}\nc? m\n{Pt0(c:C) = 3}\n"];
    1 -> 3;
  }

Communication grain (C)

  $ protocol print --project C --actions --grain communication <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   forall c in C
  >     p.a = 1;
  >     p->c: m;
  >     c.b = 1;
  >     c->p: m
  > EOF
  digraph G {
    1 [label="CReceiveM1\n{start(Ct0(p:P))}\np? m\n{Ct0(p:P) = 1}\n"];
    2 [label="CChangeB2\n{Ct0(p:P) = 1}\nb = 1;\np! m\n{Ct0(p:P) = 3}\n"];
    1 -> 2;
  }

Statement grain

  $ protocol print --project P --actions --grain statement <<EOF
  > party p in P ()
  > forall p in P
  >     p.a = 1;
  >     p.b = 2
  > EOF
  digraph G {
    1 [label="PChangeA1\n{start(Pmain)}\na = 1\n{Pmain = 1}\n"];
    2 [label="PChangeB2\n{Pmain = 1}\nb = 2\n{Pmain = 2}\n"];
    1 -> 2;
  }

Multiple parties

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > party c in C ()
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
    1 [label="PReceiveM1\n{start(Pt0(c:C))}\nc? m\n{Pt0(c:C) = 1}\n"];
    2 [label="PSendN2\n{Pt0(c:C) = 1}\nc! n\n{Pt0(c:C) = 2}\n"];
    1 -> 2;
  }

Nothing due to projection

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > party c in C ()
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

Other side

  $ protocol print --project C --actions <<EOF
  > party p in P ()
  > party c in C ()
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
    1 [label="CChangeA1\n{start(Ct0(p:P))}\na = 1;\nx = 2;\na = 3;\nx = 4\n{All([Ct0(p:P) = 2, Ct1(p:P) = 4])}\n"];
  }

TLA+

  $ protocol tla <<EOF
  > party p in P ()
  > party c in C ()
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
  
  VARIABLE history
  
  CONSTANTS C, P
  
  CONSTANTS
  
  CONSTANTS Ct0
  
  CONSTANTS
  
  Symmetry == (Permutations(C) \union Permutations(P))
  
  \* Used by C
  
  VARIABLES a, x
  
  Cvars == <<a, x>>
  
  Pvars == <<>>
  
  vars == <<a, x, messages, pc>>
  
  threads == {Ct0}
  
  participants == (C \union P)
  
  threadParticipants == {}
  
  Init ==
    /\ a = [i \in C |-> 0]
    /\ x = [i \in C |-> 0]
    /\ messages = [i \in {} |-> 0]
    /\ history = <<>>
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> 0]]
  
  CChangeA1(self) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 1]]
    /\ history' = Append(<<"CChangeA1">>, history)
    /\
      /\ a' = [a EXCEPT ![self] = 1]
      /\ x' = [x EXCEPT ![self] = 2]
      /\ a' = [a EXCEPT ![self] = 3]
      /\ x' = [x EXCEPT ![self] = 4]
    /\ UNCHANGED <<messages>>
  
  Next ==
    \/ \E self \in C : CChangeA1(self)
  
  Spec == Init /\ [][Next]_<<vars, history>>
  
  ===============================================================================


  $ protocol tla simple.spec
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
  
  VARIABLE history
  
  CONSTANTS C, P
  
  CONSTANTS c1, p1, p2
  
  CONSTANTS Ct0, Cmain, Pt1
  
  CONSTANTS prepare, prepared, abort
  
  Symmetry == (Permutations(C) \union Permutations(P))
  
  \* Used by C
  
  VARIABLES a, b
  
  Cvars == <<a, b>>
  
  Pvars == <<>>
  
  vars == <<a, b, messages, pc>>
  
  threads == {Ct0, Cmain, Pt1}
  
  participants == (C \union P)
  
  threadParticipants == {<<Ct0, p2>>, <<Ct0, p1>>, Cmain, <<Pt1, c1>>}
  
  Init ==
    /\ a = [i \in C |-> 0]
    /\ b = [i \in C |-> 0]
    /\ messages = [i \in {} |-> 0]
    /\ history = <<>>
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> 0]]
  
  CSendPrepare1(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 1]]
    /\ history' = Append(<<"CSendPrepare1", p>>, history)
    /\ messages' = Send([mtype |-> prepare, msrc |-> self, mdest |-> p], messages)
    /\ UNCHANGED <<a, b>>
  
  CReceivePrepared2(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 2]]
    /\ history' = Append(<<"CReceivePrepared2", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepared
      /\ m.mdest = self
    /\ UNCHANGED <<a, b, messages>>
  
  CChangeA3(self) ==
    /\ pc[self][<<Ct0, p>>] = 2
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 3]]
    /\ history' = Append(<<"CChangeA3">>, history)
    /\ a' = [a EXCEPT ![self] = 1]
    /\ UNCHANGED <<b, messages>>
  
  CReceiveAbort4(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 4]]
    /\ history' = Append(<<"CReceiveAbort4", p>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = abort
      /\ m.mdest = self
    /\ UNCHANGED <<a, b, messages>>
  
  CChangeA5(self) ==
    /\ pc[self][<<Ct0, p>>] = 4
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 5]]
    /\ history' = Append(<<"CChangeA5">>, history)
    /\ a' = [a EXCEPT ![self] = 2]
    /\ UNCHANGED <<b, messages>>
  
  CChangeB6(self) ==
    /\ \A pi \in P :
      \/ pc[self][<<Ct0, pi>>] = 3
      \/ pc[self][<<Ct0, pi>>] = 5
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![Cmain] = 6]]
    /\ history' = Append(<<"CChangeB6">>, history)
    /\ b' = [b EXCEPT ![self] = 3]
    /\ UNCHANGED <<a, messages>>
  
  PReceivePrepare7(self, c) ==
    /\ pc[self][<<Pt1, c>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt1, c>>] = 7]]
    /\ history' = Append(<<"PReceivePrepare7", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = prepare
      /\ m.mdest = self
    /\ UNCHANGED <<a, b, messages>>
  
  PSendPrepared8(self, c) ==
    /\ pc[self][<<Pt1, c>>] = 7
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt1, c>>] = 8]]
    /\ history' = Append(<<"PSendPrepared8", c>>, history)
    /\ messages' = Send([mtype |-> prepared, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<a, b>>
  
  PSendAbort9(self, c) ==
    /\ pc[self][<<Pt1, c>>] = 7
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt1, c>>] = 9]]
    /\ history' = Append(<<"PSendAbort9", c>>, history)
    /\ messages' = Send([mtype |-> abort, msrc |-> self, mdest |-> c], messages)
    /\ UNCHANGED <<a, b>>
  
  Next ==
    \/ \E self \in C : \E p \in P : CSendPrepare1(self, p)
    \/ \E self \in C : \E p \in P : CReceivePrepared2(self, p)
    \/ \E self \in C : CChangeA3(self)
    \/ \E self \in C : \E p \in P : CReceiveAbort4(self, p)
    \/ \E self \in C : CChangeA5(self)
    \/ \E self \in C : CChangeB6(self)
    \/ \E self \in P : \E c \in C : PReceivePrepare7(self, c)
    \/ \E self \in P : \E c \in C : PSendPrepared8(self, c)
    \/ \E self \in P : \E c \in C : PSendAbort9(self, c)
  
  Spec == Init /\ [][Next]_<<vars, history>>
  
  ===============================================================================


  $ cat simple.cfg
  
  CONSTANTS
    C = {c1}
    c1 = c1
    P = {p1, p2}
    p1 = p1
    p2 = p2
    prepare = prepare
    prepared = prepared
    abort = abort
    Ct0 = Ct0
    Cmain = Cmain
    Pt1 = Pt1
  SYMMETRY Symmetry
  SPECIFICATION Spec
  VIEW vars
  \* INVARIANT Inv

