
protocol f() (

  //((forall p in P
  //  p.a = 1)
  //\/ (forall p in P
  //  p.d = 1));

  (forall p in P
    p.a = 1;
    $f()
  )
  \/ 
  (forall p in P
    p.b = 2);
  (forall p in P
    p.c = 3)
)
forall p in P
  (forall c in C
    c->p: m); // toggle this
    $f()