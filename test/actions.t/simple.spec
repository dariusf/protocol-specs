forall c in C
  (forall p in P
    c->p: prepare;
    (p->c: prepared;
     c.a = 1
     \/
     p->c: abort;
     c.a = 2));
  c.b = 3
  