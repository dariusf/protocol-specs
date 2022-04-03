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
      p->c: abort_ack(p=p);
      aborted = union(aborted, {p})
   else
    forall p in P
      c->p: commit;
      p->c: commit_ack(p=p);
      committed = union(committed, {p})
   end)

ltl ([] (size(committed) + size(aborted) == size(P) ==>
  committed == {} | aborted == {}))
