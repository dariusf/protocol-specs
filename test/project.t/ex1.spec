forall c in C
  forall p in P
    c->p: m;
    (forall d in D
      p->d: n(c=c);
      d->c: msg);
    c.a = 1