Incomplete recursion example

Projection for functions has to be solved before --actions will work

  $ protocol print fns.spec --parties P,C
  protocol f() (
    forall p in P
      p.a = 1;
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
    ||
    forall p in (P \ {self})
      $f()
  )
  (forall c in C
     c-> : m);
  $f()

  $ protocol print fns.spec --parties P,C --project C
  protocol f() (
    skip
  )
  forall p in P
    ->p : m
