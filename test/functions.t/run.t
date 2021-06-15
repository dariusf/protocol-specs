Incomplete recursion example

Projection for functions has to be solved before --actions will work

  $ protocol print fns.spec --parties P,C --project P
  (forall c in C
     c-> : m);
  $f()
  ||
  forall p in (P \ {self})
    $f()
