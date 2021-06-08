Simplest example

  $ protocol print --parties C,P --project C <<EOF
  > forall c in C
  >   forall p in P
  >     c->p: m;
  >     p->c: n
  > EOF
  forall p in P
    ->p: m;
    p->: n

  $ protocol print --parties C,P --project P <<EOF
  > forall c in C
  >   forall p in P
  >     c->p: m;
  >     p->c: n
  > EOF
  forall c in C
    c->: m;
    ->c: n

  $ protocol print --parties C,P --project P <<EOF
  > forall c in C
  >   c.s = P;
  >   forall p in c.s
  >     c->p: m
  > EOF
  forall c in C
    c->: m

A seq involving a particular party (C), where there's a chain of messages in the middle that does not go through or end at C.

  $ protocol print --parties P,C,D basic.spec
  forall c in C
    forall p in P
      c->p: m;
      (forall d in D
         p->d: n);
      c.a = 1

The chain disappears entirely from C.

  $ protocol print --parties P,C,D --project C basic.spec
  forall p in P
    ->p: m;
    a = 1

  $ protocol print --parties P,C,D --project P basic.spec
  forall c in C
    c->: m;
    (forall d in D
       ->d: n)

  $ protocol print --parties P,C,D --project D basic.spec
  forall c in C
    forall p in P
      p->: n

A chain of messages that goes through C but does not end at it.

  $ protocol print --parties P,C,D three.spec
  forall p in P
    forall c in C
      c->p: m1;
      (forall d in D
         p->d: m2(c=c);
         d->c: m3(p=p);
         c->p: m4(d=d);
         p->d: m5);
      c.a = 1

  $ protocol print --parties P,C,D --project C three.spec
  forall p in P
    ->p: m1;
    (forall d in D
       d->: m3(p);
       ->p: m4(d=d));
    a = 1

  $ protocol print --parties P,C,D --project P three.spec
  forall c in C
    c->: m1;
    (forall d in D
       ->d: m2(c=c);
       c->: m4(d);
       ->d: m5)

  $ protocol print --parties P,C,D --project D three.spec
  forall p in P
    forall c in C
      p->: m2(c);
      ->c: m3(p=p);
      p->: m5

A chain of messages that ends at C.

  $ protocol print --parties P,C,D ex1.spec
  forall c in C
    forall p in P
      c->p: m;
      (forall d in D
         p->d: n(c=c);
         d->c: msg);
      c.a = 1

  $ protocol print --parties P,C,D --project C ex1.spec
  forall p in P
    ->p: m;
    (forall d in D
       d->: msg);
    a = 1

  $ protocol print --parties P,C,D --project P ex1.spec
  forall c in C
    c->: m;
    (forall d in D
       ->d: n(c=c))

  $ protocol print --parties P,C,D --project D ex1.spec
  forall c in C
    forall p in P
      p->: n(c);
      ->c: msg

Multiple uses of the same party set

  $ protocol print --parties C --project C - <<EOF
  > forall c in C
  >   forall d in C
  >     c->d: m
  > EOF
  error at line 3, col 4:
  self-send not allowed

  $ protocol print --parties C --project C - <<EOF
  > forall d in C
  >   forall c in C
  >     c->d: m
  > EOF
  error at line 3, col 4:
  self-send not allowed

  $ protocol print --parties C,P --project C - <<EOF
  > forall c in C
  >   forall p in P
  >     forall d in C
  >       p->d: m
  > EOF
  forall p in P
    p->: m

  $ protocol print --parties C,P --project P - <<EOF
  > forall c in C
  >   forall p in P
  >     forall d in C
  >       p->d: m
  > EOF
  forall c in C
    forall d in C
      ->d: m
