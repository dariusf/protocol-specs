These two have the same precedence and associativity.

  $ protocol print --parties C,P --project C <<EOF
  > forall c in C
  >   forall p in P
  >     c->p: m;
  >     p->c: n
  > EOF
  forall p in P
    *self->p: m;
    p->self*: n

  $ protocol print --parties C,P --project P <<EOF
  > forall c in C
  >   forall p in P
  >     c->p: m;
  >     p->c: n
  > EOF
  forall c in C
    c->self*: m;
    *self->c: n

This is incomplete

  $ protocol print --parties C,P --project P <<EOF
  > forall c in C
  >   c.s = P;
  >   forall p in c.s
  >     c->p: m
  > EOF
  forall c in C
    c->self*: m
