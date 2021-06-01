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
    0 [label="λ c:C.\nc->self*: m"];
    1 [label="λ c:C.\n*self->c: n"];
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
    0 [label="c.a = 1;\nc.x = 2"];
    1 [label="c.a = 3;\nc.x = 4"];
    0 -> 1;
  }

  $ protocol tla --parties P,C --project C <<EOF
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

  $ cat -- '-.tla'
  
  --------------------------------- MODULE - ---------------------------------
  
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
  
  
  CONSTANT P
  
  CONSTANT C
  
  Pvars == <<>>
  
  Cvars == <<a, x>>
  
  vars == <<a, x, messages>>
  
  \* Used by C
  
  VARIABLES a x
  
  Init ==
    /\ a = [i \in C |-> 0]
    /\ x = [i \in C |-> 0]
  
  CChangeA0(self) ==
    /\ pc' = [pc EXCEPT ![self] = 0]
    /\ 
      /\ a' = [a EXCEPT ![self] = 1]
      /\ x' = [x EXCEPT ![self] = 2]
    /\ UNCHANGED <<messages>>
  
  CChangeA1(self) ==
    /\ pc = 0
    /\ pc' = [pc EXCEPT ![self] = 1]
    /\ 
      /\ a' = [a EXCEPT ![self] = 3]
      /\ x' = [x EXCEPT ![self] = 4]
    /\ UNCHANGED <<messages>>
  
  Next ==
    \/ \E self \in C : CChangeA0(self)
    \/ \E self \in C : CChangeA1(self)
  
  Spec == Init /\ [][Next]_vars
  
  ===============================================================================
