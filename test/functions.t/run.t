Recursion example

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
     c? m);
  $f()

  $ protocol print fns.spec --project C
  protocol f() (
    $f()
  )
  (forall p in P
     p! m);
  $f()

  $ protocol print fns.spec --project P --actions
  digraph G {
    1 [label="PChangeA1\n{Pmain = 1}\na = 1\n{Pmain = 1}\n"];
    4 [label="PReceiveM4\n{start(Pt0(c:C))}\nc? m\n{Pmain = 1}\n"];
    4 -> 1;
    1 -> 1;
  }

  $ protocol print fns.spec --project C --actions
  digraph G {
    3 [label="CSendM3\n{start(Ct0(p:P))}\np! m\n{Cmain = 1}\n"];
  }

$ protocol tla fns.spec
fns.tla
fns.cfg

$ cat fns.tla
