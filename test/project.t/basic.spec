party p in P ()
party c in C ()
party d in D ()

forall c in C
  forall p in P
    c->p: m;
    (forall d in D
      p->d: n);
    c.a = 1