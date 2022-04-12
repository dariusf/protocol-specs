
party u in U (u.parties = {})

forall u in U
  forall v in U
    u->v: m;
    u.parties = union(u.parties, {u});
    v.parties = union(u.parties, {u})