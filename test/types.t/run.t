Variables bound by forall disappear.

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  > (forall c in C
  >   c.a = 1);
  > forall p in P
  >   p.b = c
  > EOF
  error at line 6, col 8:
  unbound variable c

Local variables disappear after the sequence they are in is terminated.

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  > (forall c in C
  >   forall p in P
  >     c->p: m;
  >     p.a = union(a, {c}));
  > forall p in C
  >   p.b = c
  > EOF
  error at line 8, col 8:
  unbound variable c

Message variables are also local.

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     c->p: m(a=1);
  >     p.b = a
  > EOF
  forall (c : party C;global) in (C : map(party C, bool);global)
    forall (p : party P;global) in (P : map(party P, bool);global)
      (c : party C;global)->(p : party P;global) : m((a : int;P)=1);
      (p.b : int;P) = (p.a : int;P)

We can't tell which party r belongs to because c is global.

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     r = union(r, {c})
  > EOF
  error at line 5, col 4:
  failed to infer party for r

Qualifying r allows us to infer the type.

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  > forall c in C
  >   forall p in P
  >     r = union(p.r, {c});
  >     c->p: m
  > EOF
  forall (c : party C;global) in (C : map(party C, bool);global)
    forall (p : party P;global) in (P : map(party P, bool);global)
      (p.r : map(party C, bool);P) = union((p.r : map(party C, bool);P), {(c : party C;global)});
      (c : party C;global)->(p : party P;global) : m

Here it's not possible for members of party C to know which of them should send a message to P because they don't know s, which resides on p...

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  >  forall p in P
  >   p.s = C;
  >   forall x in p.s
  >     x->p: m
  > EOF
  error at line 6, col 4:
  sender x does not know of itself (of party C but known only to P)

... but it becomes possible if p first sends a message to members of x to inform them of its existence.

  $ protocol print --types <<EOF
  > party p in P ()
  > party c in C ()
  > forall p in P
  >   p.s = C;
  >   forall x in p.s
  >     p->x: n(x=x);
  >     x->p: m
  > EOF
  forall (p : party P;global) in (P : map(party P, bool);global)
    (p.s : map(party C, bool);P) = (C : map(party C, bool);global);
    (forall (x : party C;P) in (p.s : map(party C, bool);P)
       (p : party P;global)->(x : party C;P) : n((x : party C;C)=(x : party C;P));
       (x : party C;C)->(p : party P;global) : m)

This fails because we cannot infer a type for a...

  $ protocol print --types <<EOF
  > party c in C (c.a = {})
  > (forall c in C
  >   c.a = {})
  > EOF
  error at line -1, col -1:
  failed to infer type for a

... but this should work.

  $ protocol print --types <<EOF
  > party c in C ()
  > (forall c in C
  >   c.a = {});
  > forall c in C
  >   c.a = union(c.a, {c})
  > EOF
  (forall (c : party C;global) in (C : map(party C, bool);global)
     (c.a : map(party C, bool);C) = {});
  (forall (c : party C;global) in (C : map(party C, bool);global)
     (c.a : map(party C, bool);C) = union((c.a : map(party C, bool);C), {(c : party C;global)}))

  $ protocol print --types <<EOF
  > party c in C (c.a = 1)
  > party p in P ()
  > forall p in P
  >   forall c in C
  >     c->p: m(x=c.a);
  >     b = x
  (forall (c : party C;global) in (C : map(party C, bool);global)
     (c.a : int;C) = 1);
  (forall (p : party P;global) in (P : map(party P, bool);global)
     forall (c : party C;global) in (C : map(party C, bool);global)
       (c : party C;global)->(p : party P;global) : m((x : int;P)=(c.a : int;C));
       (p.b : int;P) = (p.x : int;P))
