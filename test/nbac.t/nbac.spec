// A Case Study of Agreement Problems in Distributed Systems: Non-Blocking Atomic Commitment (1997)

forall f in F
  forall p in P
    // timeout =>* // this is unnecessary but expresses intent
      (f->p : exception(id=p);
       p.some_failed = true
       \/
       f->p : ok)
||
forall p in P
  forall q in P
    (p->q : yes;
     q.voted_yes = union(q.voted_yes, {p})
     \/
     p->q : no;
     q.no = true)
||
forall p in P
  (p.no | p.some_failed =>*
     p.outcome = "abort"
   \/
   p.voted_yes == P =>*
     p.outcome = "commit")
