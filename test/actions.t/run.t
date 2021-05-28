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
    0 [label="λ c.\nc->self*: m"];
    1 [label="λ c.\n*self->c: n"];
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
    0 [label="λ p.\nc.a = 1;\nc.x = 2"];
    1 [label="λ p.\nc.a = 3;\nc.x = 4"];
    0 -> 1;
  }
