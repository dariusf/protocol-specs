
forall c in C
  (forall p in P
    c->p: prepare;

    (p->c: prepared;
     responded = union(responded, {p})
     \/
     p->c: abort;
     aborted = union(aborted, {p})))
  ||

  // these outcomes are disjoint, so continue as soon as one becomes true
  (responded == P =>*
     forall p in P
       c->p: commit;
       p->c: commit_ack
   \/
   aborted != {} =>*
     forall p in P
       c->p: abort;
       p->c: abort_ack)
