Incomplete recursion example

Projection for functions has to be solved before --actions will work

  $ protocol print fns.spec
  (forall p in P
     forall c in C
       c->p : m);
  $f()

  $ protocol print fns.spec --project P
  protocol f() (
    a = 1;
    $f()
  )
  (forall c in C
     c-> : m);
  $f()

  $ protocol print fns.spec --project C
  protocol f() (
    $f()
  )
  (forall p in P
     ->p : m);
  $f()

  $ protocol print fns.spec --project P --actions
  digraph G {
    1 [label="PChangeA1\n{Pmain = 1}\na = 1\n{Pmain = 1}\n"];
    4 [label="PReceiveM4\n{start}\nc→ : m\n{Pmain = 1}\n"];
    4 -> 1;
    1 -> 1;
  }

  $ protocol print fns.spec --project C --actions
  digraph G {
    1 [label="CDummy1\n{Cmain = 1}\nskip\n{Cmain = 1}\n"];
    3 [label="CSendM3\n{start}\n→p : m\n{Cmain = 1}\n"];
    3 -> 1;
    1 -> 1;
  }

$ protocol tla fns.spec
fns.tla
fns.cfg

$ cat fns.tla
