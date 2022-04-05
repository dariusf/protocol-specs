party p in P ()
party c in C ()

protocol f() (
  (forall p in P
    p.a = 1);
  $f()
)
(forall p in P
  (forall c in C
    c->p: m));
$f()