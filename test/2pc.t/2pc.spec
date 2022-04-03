forall c in C
  (forall p in P
    c->p: prepare;
    (p->c: prepared
     \/
     p->c: abort;
     c.has_aborted = true));
  (if has_aborted then
    forall p in P
      c->p: abort;
      p->c: abort_ack;
      c.aborted = union(c.aborted, {p})
   else
    forall p in P
      c->p: commit;
      p->c: commit_ack;
      c.committed = union(c.committed, {p})
   end)

ltl ([] (size(committed) + size(aborted) == size(P) ==>
  committed == {} | aborted == {}))
