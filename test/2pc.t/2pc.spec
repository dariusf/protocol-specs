
forall c in C
  (forall p in P
    c->p: prepare;

    // participant's internal choice
    // coordinator's external choice
    (p->c: prepared;
    responded = union(responded, {p})
    \/
    p->c: abort;
    aborted = union(aborted, {p})));
  aborted == {} =>*
    (forall p in P
      c->p: commit;
      p->c: commit_ack
    \/
    forall p in P
      c->p: abort;
      p->c: abort_ack)