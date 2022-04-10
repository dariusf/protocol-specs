Simplest multiparty examples

  $ protocol print --project C <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   p.a = 1
  > EOF
  skip

  $ protocol print --project P <<EOF
  > party p in P ()
  > forall p in P
  >   p.a = 1
  > EOF
  a = 1

  $ protocol print --project C <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     c->p: m;
  >     p->c: n
  > EOF
  forall p in P
    p! m;
    p? n

  $ protocol print --project P <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     c->p: m;
  >     p->c: n
  > EOF
  forall c in C
    c? m;
    c! n

Dynamic party set (i.e. types are used to compute projection)

  $ protocol print --project P <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   c.s = P;
  >   forall p in c.s
  >     c->p: m
  > EOF
  forall c in C
    c? m

A seq involving a particular party C, where there's a chain of messages in the middle that does not go through or end at C.

  $ protocol print basic.spec
  forall c in C
    forall p in P
      c->p : m;
      (forall d in D
         p->d : n);
      c.a = 1

The chain disappears entirely from C.

  $ protocol print --project C basic.spec
  forall p in P
    p! m;
    a = 1

  $ protocol print --project P basic.spec
  forall c in C
    c? m;
    (forall d in D
       d! n)

  $ protocol print --project D basic.spec
  forall c in C
    forall p in P
      p? n

A chain of messages that goes through C but does not end at it.

  $ protocol print three.spec
  forall p in P
    forall c in C
      c->p : m1;
      (forall d in D
         p->d : m2;
         d->c : m3;
         c->p : m4;
         p->d : m5);
      c.a = 1

  $ protocol print --project C three.spec
  forall p in P
    p! m1;
    (forall d in D
       d? m3;
       p! m4);
    a = 1

  $ protocol print --project P three.spec
  forall c in C
    c? m1;
    (forall d in D
       d! m2;
       c? m4;
       d! m5)

  $ protocol print --project D three.spec
  forall p in P
    forall c in C
      p? m2;
      c! m3;
      p? m5

A chain of messages that ends at C.

  $ protocol print ex1.spec
  forall c in C
    forall p in P
      c->p : m;
      (forall d in D
         p->d : n(c=c);
         d->c : msg);
      c.a = 1

  $ protocol print --project C ex1.spec
  forall p in P
    p! m;
    (forall d in D
       d? msg);
    a = 1

  $ protocol print --project P ex1.spec
  forall c in C
    c? m;
    (forall d in D
       d! n(c=c))

  $ protocol print --project D ex1.spec
  forall c in C
    forall p in P
      p? n(c);
      c! msg

This projects and typechecks, but likely isn't what was meant.

  $ protocol print --types <<EOF
  > party c in C (c.leader = true)
  > party p in P ()
  > forall p in P
  >   forall c in C
  >     c.leader =>*
  >       p->c: m
  (forall (c : party C;global) in (C : map(party C, bool);global)
     (c.leader : bool;C) = true);
  (forall (p : party P;global) in (P : map(party P, bool);global)
     forall (c : party C;global) in (C : map(party C, bool);global)
       (c.leader : bool;C) =>*
         (p : party P;global)->(c : party C;global) : m)

  $ protocol print --project P <<EOF
  > party c in C (c.leader = true)
  > party p in P ()
  > forall p in P
  >   forall c in C
  >     c.leader =>*
  >       p->c: m
  forall c in C
    c! m

  $ protocol print --project C <<EOF
  > party c in C (c.leader = true)
  > party p in P ()
  > forall p in P
  >   forall c in C
  >     c.leader =>*
  >       p->c: m
  leader = true;
  (forall p in P
     leader =>*
       p? m)

Multiple uses of the same party set, aka self-sends within a role.

Classic example from the paper.

Given a set of 3 parties, there will be 2 sends and 2 receives per party.

In parallel, send to everyone but us, and receive from everyone but us.
Only on the receiving end do we set the a to 1.

  $ protocol print --project C - <<EOF
  > party c in C ()
  > forall c in C
  >   forall d in (C \ {c})
  >     c->d: m;
  >     d.a = 1;
  >     c.b = 2
  > EOF
  forall d in (C \ {self})
    d! m;
    b = 2
  ||
  forall c in (C \ {self})
    c? m;
    a = 1

Sending to ourselves as well. Now there will be 3 sends and 3 receives per party.

  $ protocol print --project C - <<EOF
  > party c in C ()
  > forall c in C
  >   forall d in C
  >     c->d: m;
  >     d.a = 1;
  >     c.b = 2
  > EOF
  self! m;
  self? m;
  a = 1;
  b = 2
  ||
  forall d in (C \ {self})
    d! m;
    b = 2
  ||
  forall c in (C \ {self})
    c? m;
    a = 1

Explicit self-send

  $ protocol print --project C - <<EOF
  > party c in C ()
  > forall c in C
  >   c->c: m;
  >   forall d in (C \ {c})
  >     c->d: m
  > EOF
  self! m;
  self? m;
  (forall d in (C \ {self})
     d! m)
  ||
  forall c in (C \ {self})
    c? m

Literal self-send

  $ protocol print --project C - <<EOF
  > party c in C ()
  > forall c in C
  >   c->c: m
  > EOF
  self! m;
  self? m

Unintuitive example. If |C| = 1, only one message is received from P (in the first thread).
If |C| = 2, both threads receive messages.

  $ protocol print --project C - <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     forall d in C
  >       p->d: m
  > EOF
  forall p in P
    p? m
  ||
  forall c in (C \ {self})
    forall p in P
      p? m

  $ protocol print --project P - <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     forall d in C
  >       p->d: m
  > EOF
  forall c in C
    forall d in C
      d! m

More standard variations

  $ protocol print --project C - <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   forall d in C
  >     p->d: m
  > EOF
  forall p in P
    p? m

  $ protocol print --project C - <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     forall d in (C \ {c})
  >       p->d: m
  > EOF
  forall c in (C \ {self})
    forall p in P
      p? m

More than two self-sends

  $ protocol print --project C - <<EOF
  > party c in C ()
  > forall c in C
  >   forall d in C
  >     forall e in C
  >       e->d: m
  > EOF
  self! m;
  self? m
  ||
  forall e in (C \ {self})
    e? m
  ||
  forall d in (C \ {self})
    d! m
  ||
  forall c in (C \ {self})
    (self! m;
     self? m
     ||
     forall e in (C \ {self})
       e? m
     ||
     forall d in (C \ {self})
       d! m)

Self-send with conditions. Shows that we also need to consider if the owner of an expression is self when projecting.

  $ protocol print --project C - <<EOF
  > party c in C (
  >   c.leader = false
  > )
  > forall c in C
  >   forall d in (C \\ {c})
  >     c.leader =>*
  >       c->d: m
  > EOF
  leader = false;
  (forall d in (C \ {self})
     leader =>*
       d! m
   ||
   forall c in (C \ {self})
     c? m)

Why are the following cases different?

  $ protocol print --project C - <<EOF
  > party c in C (
  >   c.a = false;
  >   c.b = false
  > )
  > forall c in C
  >   forall d in (C \\ {c})
  >     c.a = true;
  >     d.b = true
  > EOF
  a = false;
  b = false;
  (forall d in (C \ {self})
     a = true
   ||
   forall c in (C \ {self})
     b = true)

  $ protocol print --project C - <<EOF
  > party c in C (
  >   c.a = false;
  >   c.b = false
  > )
  > forall c in C
  >   c.a = true;
  >   forall d in (C \\ {c})
  >     d.b = true
  > EOF
  a = false;
  b = false;
  (a = true
   ||
   forall c in (C \ {self})
     b = true)

Conditional using expressions from the different parties, but same set. We could split the expression, but it doesn't seem meaningful to do so, as 1. if they're from the same set, this is useless, and 2. if they're from different sets, this can't be checked.

  $ protocol print --project C - <<EOF
  > party c in C (
  >   c.a = true;
  >   c.b = true
  > )
  > forall c in C
  >   c.a = false;
  >   forall d in (C \\ {c})
  >     d.b = false;
  >     c.a and d.b =>*
  >       c->d: m
  > EOF
  error at line 9, col 4:
  self.a & d.b must have a single location
