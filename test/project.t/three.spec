party p in P ()
party c in C ()
party d in D ()

forall p in P
  forall c in C
    c->p: m1;
    (forall d in D
      p->d: m2;
      d->c: m3;
      c->p: m4;
      p->d: m5
      );
    c.a = 1