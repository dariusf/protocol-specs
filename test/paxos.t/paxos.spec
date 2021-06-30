// all currently-competing proposers
(forall p in P
  p.proposal = 0;
  p.value = 1;
  p.cp = [0, 0];
  p.majority = size(A) / 2 + 1;
  p.promise_responses = {});

(forall a in A
  // a.highest_proposal = [0, 0];
  a.highest_proposal = 0;
  // a.accepted_proposal = [0, 0];
  a.accepted_proposal = 0;
  a.accepted_value = 0);

forall p in P
  (p.proposal = p.proposal + 1;
  forall a in A
    // p->a: prepare(n=[p, p.proposal]);
    p->a: prepare(n=p2i(p) * 100 + p.proposal);
    n > a.highest_proposal =>
      a.highest_proposal = n;
      a->p: promise(cp=a.accepted_proposal, cv=a.accepted_value);
      p.promise_responses = union(p.promise_responses, {a});
      // if a has already accepted something
      // cp > [0, 0] & cp > p.cp =>
      cp > 0 & cp > p.cp =>
        p.cp = cp;
        p.value = cv
  ||
  // doesn't continue replying with accepts if others outside this set reply
  size(p.promise_responses) > p.majority =>*
    // it's sufficient to reply to the majority subset
    forall a1 in p.promise_responses
      p->a1: propose(pn=p.proposal, pv=p.value, a1=a1);
      pn == a1.highest_proposal =>
        a1.accepted_proposal = pn;
        a1.accepted_value = pv;
        a1->p: accept;
        forall l in L
          a1->l: accept)