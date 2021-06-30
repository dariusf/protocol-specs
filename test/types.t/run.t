Variables bound by forall disappear.

  $ protocol print --parties P,C --types <<EOF
  > (forall c in C
  >   c.a = 1);
  > forall p in P
  >   p.b = c
  > EOF
  error at line 4, col 8:
  unbound variable c

Local variables disappear after the sequence they are in is terminated.

  $ protocol print --parties P,C --types <<EOF
  > (forall c in C
  >   forall p in P
  >     c->p: m;
  >     p.a = union(a, {c}));
  > forall p in C
  >   p.b = c
  > EOF
  error at line 6, col 8:
  unbound variable c

Message variables are also local.

  $ protocol print --parties P,C --types <<EOF
  > forall c in C
  >   forall p in P
  >     c->p: m(a=1);
  >     p.b = a
  > EOF
  forall (c : party C;global) in (C : {party C};global)
    forall (p : party P;global) in (P : {party P};global)
      (c : party C;global)->(p : party P;global) : m((a : int;P)=1);
      (p.b : int;P) = (p.a : int;P)

We can't tell which party r belongs to because c is global.

  $ protocol print --parties P,C --types <<EOF
  > forall c in C
  >   forall p in P
  >     r = union(r, {c})
  > EOF
  error at line 3, col 4:
  failed to infer party for r

Qualifying r allows us to infer the type.

  $ protocol print --parties P,C --types <<EOF
  > forall c in C
  >   forall p in P
  >     r = union(p.r, {c});
  >     c->p: m
  > EOF
  forall (c : party C;global) in (C : {party C};global)
    forall (p : party P;global) in (P : {party P};global)
      (p.r : {party C};P) = union((p.r : {party C};P), {(c : party C;global)});
      (c : party C;global)->(p : party P;global) : m

Here it's not possible for members of party C to know which of them should send a message to P because they don't know s, which resides on p...

  $ protocol print --parties P,C --types <<EOF
  >  forall p in P
  >   p.s = C;
  >   forall x in p.s
  >     x->p: m
  > EOF
  error at line 4, col 4:
  sender x does not know of itself (of party C but known only to P)

... but it becomes possible if p first sends a message to members of x to inform them of its existence.

  $ protocol print --parties P,C --types <<EOF
  > forall p in P
  >   p.s = C;
  >   forall x in p.s
  >     p->x: n(x=x);
  >     x->p: m
  > EOF
  forall (p : party P;global) in (P : {party P};global)
    (p.s : {party C};P) = (C : {party C};global);
    (forall (x : party C;P) in (p.s : {party C};P)
       (p : party P;global)->(x : party C;P) : n((x : party C;C)=(x : party C;P));
       (x : party C;C)->(p : party P;global) : m)

This fails because we cannot infer a type for a...

  $ protocol print --parties C --types <<EOF
  > (forall c in C
  >   c.a = {})
  > EOF
  error at line 2, col 2:
  failed to infer type for a

... but this should work.

  $ protocol print --parties C --types <<EOF
  > (forall c in C
  >   c.a = {});
  > forall c in C
  >   c.a = union(c.a, {c})
  > EOF
  (forall (c : party C;global) in (C : {party C};global)
     (c.a : {party C};C) = {});
  (forall (c : party C;global) in (C : {party C};global)
     (c.a : {party C};C) = union((c.a : {party C};C), {(c : party C;global)}))
