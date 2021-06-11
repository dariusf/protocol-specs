forall c in C
  (forall p in P
    c->p: prepare;
    (p->c: prepared
     \/
     p->c: abort;
     c.has_aborted = true));
  (!has_aborted =>
    forall p in P
      c->p: commit;
      p->c: commit_ack;
      committed = union(committed, {p})
   \/
   has_aborted =>
    forall p in P
      c->p: abort;
      p->c: abort_ack;
      aborted = union(aborted, {p}))

ltl ([] (size(committed) + size(aborted) == size(P) ==>
  committed == {} | aborted == {}))
