forall p in P
  forall c in C
    c->p: m1;
    (forall d in D
      p->d: m2(c=c);
      d->c: m3(p=p);
      c->p: m4(d=d);
      p->d: m5
      );
    c.a = 1