Single-decree Paxos

  $ protocol print paxos.spec
  (forall p in P
     p.proposal = 0;
     p.value = 1;
     p.cp = [0, 0];
     p.majority = size(A) / 2 + 1;
     p.promise_responses = {});
  (forall a in A
     a.highest_proposal = 0;
     a.accepted_proposal = 0;
     a.accepted_value = 0);
  (forall p in P
     (p.proposal = p.proposal + 1;
      (forall a in A
         p->a: prepare(n=p2i(p) * 100 + p.proposal);
         (n > a.highest_proposal =>
            a.highest_proposal = n;
            a->p: promise(cp=a.accepted_proposal, cv=a.accepted_value);
            p.promise_responses = union(p.promise_responses, {a});
            (cp > 0 & cp > p.cp =>
               p.cp = cp;
               p.value = cv)))
      ||
      size(p.promise_responses) > p.majority =>*
        (forall a1 in p.promise_responses
           p->a1: propose(pn=p.proposal, pv=p.value);
           ac2 = a1;
           (pn == a1.highest_proposal =>
              a1.accepted_proposal = pn;
              a1.accepted_value = pv;
              a1->p: accept;
              (forall l in L
                 ac2->l: accept)))))

  $ protocol print paxos.spec --parties P,A,L --types
  (forall (p : party P;global) in (P : {party P};global)
     (p.proposal : int;P) = 0;
     (p.value : int;P) = 1;
     (p.cp : [int];P) = {0, 0};
     (p.majority : int;P) = size((A : {party A};global)) / 2 + 1;
     (p.promise_responses : {party A};P) = {});
  (forall (a : party A;global) in (A : {party A};global)
     (a.highest_proposal : int;A) = 0;
     (a.accepted_proposal : int;A) = 0;
     (a.accepted_value : int;A) = 0);
  (forall (p : party P;global) in (P : {party P};global)
     ((p.proposal : int;P) = (p.proposal : int;P) + 1;
      (forall (a : party A;global) in (A : {party A};global)
         (p : party P;global)->(a : party A;global): prepare((n : int;A)=p2i((p : party P;global)) * 100 + (p.proposal : int;P));
         ((n : int;A) > (a.highest_proposal : int;A) =>
            (a.highest_proposal : int;A) = (n : int;A);
            (a : party A;A)->(p : party P;A): promise((cp : int;P)=(a.accepted_proposal : int;A), (cv : int;P)=(a.accepted_value : int;A));
            (p.promise_responses : {party A};P) = union((p.promise_responses : {party A};P), {(a : party A;P)});
            ((cp : int;P) > 0 & (cp : int;P) > (p.cp : int;P) =>
               (p.cp : int;P) = (cp : int;P);
               (p.value : int;P) = (cv : int;P))))
      ||
      size((p.promise_responses : {party A};P)) > (p.majority : int;P) =>*
        (forall (a1 : party A;P) in (p.promise_responses : {party A};P)
           (p : party P;global)->(a1 : party A;P): propose((pn : int;A)=(p.proposal : int;P), (pv : int;A)=(p.value : int;P));
           (ac2 : party A;A) = (a1 : party A;A);
           ((pn : int;A) == (a1.highest_proposal : int;A) =>
              (a1.accepted_proposal : int;A) = (pn : int;A);
              (a1.accepted_value : int;A) = (pv : int;A);
              (a1 : party A;A)->(p : party P;A): accept;
              (forall (l : party L;global) in (L : {party L};global)
                 (ac2 : party A;A)->(l : party L;global): accept)))))

  $ protocol print paxos.spec --parties P,A,L --project P
  proposal = 0;
  value = 1;
  cp = {0, 0};
  majority = size(A) / 2 + 1;
  promise_responses = {};
  (proposal = p.proposal + 1;
   (forall a in A
      ->a: prepare(n=p2i(p) * 100 + p.proposal);
      a->: promise(cp, cv);
      promise_responses = union(p.promise_responses, {a});
      (cp > 0 & cp > p.cp =>
         cp = cp;
         value = cv))
   ||
   size(p.promise_responses) > p.majority =>*
     (forall a1 in p.promise_responses
        ->a1: propose(pn=p.proposal, pv=p.value);
        a1->: accept))

  $ protocol print paxos.spec --parties P,A,L --project A
  highest_proposal = 0;
  accepted_proposal = 0;
  accepted_value = 0;
  (forall p in P
     (p->: prepare(n);
      (n > a.highest_proposal =>
         highest_proposal = n;
         ->p: promise(cp=a.accepted_proposal, cv=a.accepted_value))
      ||
      p->: propose(pn, pv);
      ac2 = a1;
      (pn == a1.highest_proposal =>
         accepted_proposal = pn;
         accepted_value = pv;
         ->p: accept;
         (forall l in L
            ->l: accept))))

  $ protocol print paxos.spec --parties P,A,L --project L
  (forall p in P
     (forall a1 in p.promise_responses
        ac2->: accept))

  $ protocol print paxos.spec > paxos1.spec && protocol print paxos1.spec | protocol print > paxos2.spec && git diff --no-index paxos1.spec paxos2.spec
