// A Case Study of Agreement Problems in Distributed Systems: Non-Blocking Atomic Commitment (1997)

party p in P ()
party f in F ()

forall p in P
  forall q in P
    (p->q : yes;
     q.voted_yes = union(q.voted_yes, {p})
     \/
     p->q : no;
     q.no = true)
||
forall f in F
  forall p in P
    forall q in (P \ {p})
      f->p : exception(id=q);
      p.some_failed = true
||
forall p in P
  (p.no | p.some_failed =>*
     p.outcome = "abort"
   \/
   p.voted_yes == P =>*
     p.outcome = "commit")