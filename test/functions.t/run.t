Incomplete recursion example

Projection for functions has to be solved before --actions will work

  $ protocol print fns.spec --parties P,C
  protocol f() (
    (forall p in P
       p.a = 1);
    $f()
  )
  (forall p in P
     forall c in C
       c->p : m);
  $f()

  $ protocol print fns.spec --parties P,C --project P
  protocol f() (
    a = 1;
    $f()
  )
  (forall c in C
     c-> : m);
  $f()

  $ protocol print fns.spec --parties P,C --project C
  protocol f() (
    $f()
  )
  (forall p in P
     ->p : m);
  $f()

  $ protocol print fns.spec --parties P,C --project P --actions
  digraph G {
    1 [label="PChangeA1\n{Pmain = 1}\na = 1\n{Pmain = 1}\n"];
    4 [label="PReceiveM4\n{start}\nc→ : m\n{Pmain = 1}\n"];
    4 -> 1;
    1 -> 1;
  }

  $ protocol print fns.spec --parties P,C --project C --actions
  digraph G {
    1 [label="CDummy1\n{Cmain = 1}\nskip\n{Cmain = 1}\n"];
    3 [label="CSendM3\n{start}\n→p : m\n{Cmain = 1}\n"];
    3 -> 1;
    1 -> 1;
  }

  $ protocol tla fns.spec --parties P,C
  fns.tla
  fns.cfg

  $ cat fns.tla
  
  --------------------------------- MODULE fns ---------------------------------
  
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
  
  CONSTANTS Ct1, Ct0, Pt3, Pt2
  
  CONSTANTS m
  
  Symmetry == (Permutations(C) \union Permutations(P))
  
  Cvars == <<>>
  
  Pvars == <<>>
  
  vars == <<messages, pc>>
  
  threads == {Ct1, Ct0, Pt3, Pt2}
  
  participants == (C \union P)
  
  threadParticipants == {}
  
  Init ==
    /\ messages = [i \in {} |-> 0]
    /\ history = <<>>
    /\ pc = [i \in participants |-> [j \in threadParticipants |-> 0]]
  
  CChangeA1(self) ==
    /\ pc[self][Cmain] = 1
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct1, p>>] = 1]]
    /\ history' = Append(<<"CChangeA1">>, history)
    /\ a' = [a EXCEPT ![self] = 1]
    /\ UNCHANGED <<messages>>
  
  CSendM4(self, p) ==
    /\ pc[self][<<Ct0, p>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Ct0, p>>] = 4]]
    /\ history' = Append(<<"CSendM4", p>>, history)
    /\ messages' = Send([mtype |-> m, msrc |-> self, mdest |-> p], messages)
  
  PChangeA6(self) ==
    /\ pc[self][Pmain] = 6
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt3, p>>] = 6]]
    /\ history' = Append(<<"PChangeA6">>, history)
    /\ a' = [a EXCEPT ![self] = 1]
    /\ UNCHANGED <<messages>>
  
  PReceiveM9(self, c) ==
    /\ pc[self][<<Pt2, c>>] = 0
    /\ pc' = [pc EXCEPT ![self] = [pc[self] EXCEPT ![<<Pt2, c>>] = 9]]
    /\ history' = Append(<<"PReceiveM9", c>>, history)
    /\ \E m \in DOMAIN messages :
      /\ (messages[m] > 0)
      /\ m.mtype = m
      /\ m.mdest = self
    /\ UNCHANGED <<messages>>
  
  Next ==
    \/ \E self \in C : CChangeA1(self)
    \/ \E self \in C : \E p \in P : CSendM4(self, p)
    \/ \E self \in P : PChangeA6(self)
    \/ \E self \in P : \E c \in C : PReceiveM9(self, c)
  
  Spec == Init /\ [][Next]_<<vars, history>>
  
  ===============================================================================
