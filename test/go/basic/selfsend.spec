
party t in T (t.parties = {})

forall t in T
  forall u in (T \ {t})
    t->u: m;
    t.parties = union(t.parties, {t});
    u.parties = union(u.parties, {t})