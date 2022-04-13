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
    4 [label="PReceiveM4\n{Pt0(c:C) = start}\nc? m\n{All([Pt0(c:C) = 4, Pmain = 1])}\n"];
    4 -> 1;
    1 -> 1;
  }

  $ protocol print fns.spec --project C --actions
  digraph G {
    3 [label="CSendM3\n{Ct0(p:P) = start}\np! m\n{All([Ct0(p:P) = 3, Cmain = 1])}\n"];
  }

$ protocol tla fns.spec
fns.tla
fns.cfg

$ cat fns.tla

Call under par. The main thread of f should be that of its (one, for now) caller.

  $ protocol print --project P --actions <<EOF
  > party p in P ()
  > protocol f() (
  >   (forall p in P p.a = 1);
  >   \$f
  > )
  > protocol g() (
  >   (forall p in P p.a = 1);
  >   \$g
  > )
  > \$f || \$g
  > EOF
  digraph G {
    1 [label="PChangeA1\n{Pt1 = 1}\na = 1\n{Pt1 = 1}\n"];
    2 [label="PChangeA2\n{Pt0 = 2}\na = 1\n{Pt0 = 2}\n"];
    7 [label="PCall7\n{Pt0 = start}\n$f()\n{Pt0 = 2}\n"];
    8 [label="PCall8\n{Pt1 = start}\n$g()\n{Pt1 = 1}\n"];
    8 -> 1;
    7 -> 2;
    2 -> 2;
    1 -> 1;
  }

$ protocol print --project P --actions <<EOF
> party p in P ()
> protocol f() (
>   
> )
> forall p in P (p.a = 1)
> EOF

> protocol f() (
>   (forall p in P
>     p.a = 1);
>   $f
> )

> protocol g() (
>   forall p in P
>     p.b = 2
> )
digraph G {
}
