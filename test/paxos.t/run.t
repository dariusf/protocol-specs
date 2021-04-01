Single-decree Paxos

  $ protocol print paxos.spec
  (forall p in P
     p.proposal = 0;
     p.value = external();
     p.cp = [0, 0];
     p.majority = size(A) / 2 + 1;
     p.promise_responses = {});
  (forall a in A
     a.highest_proposal = [0, 0];
     a.accepted_proposal = [0, 0];
     a.accepted_value = 0);
  (forall p in P
     p.proposal = p.proposal + 1;
     (forall a in A
        p->a: prepare(n=[p, p.proposal]);
        (n > a.highest_proposal =>
           a.highest_proposal = n;
           a->p: promise(cp=a.accepted_proposal, cv=a.accepted_value);
           p.promise_responses = p.promise_responses + {a};
           (cp > [0, 0] & cp > p.cp =>
              p.cp = cp;
              p.value = cv)))
     ||
     size(p.promise_responses) > p.majority =>*
       forall a1 in p.promise_responses
         p->a1: propose(pn=p.proposal, pv=p.value);
         (pn == a1.highest_proposal =>
            a1.accepted_proposal = pn;
            a1.accepted_value = pv;
            a1->p: accept;
            (forall l in L
               a1->l: accept)))

  $ protocol print paxos.spec --party P:p:a,p,proposal,value,majority,promise_responses,cp,cv: --party L:l:: --party A:a,a1:p,highest_proposal,accepted_proposal,accepted_value,n,pn,pv: --project P
  p.proposal = 0;
  p.value = external();
  p.cp = [0, 0];
  p.majority = size(A) / 2 + 1;
  p.promise_responses = {};
  (p.proposal = p.proposal + 1;
   (forall a in A
      *self->a: prepare([p, p.proposal]);
      a->self*: promise(cp, cv);
      p.promise_responses = p.promise_responses + {a};
      (cp > [0, 0] & cp > p.cp =>
         p.cp = cp;
         p.value = cv))
   ||
   size(p.promise_responses) > p.majority =>*
     forall a1 in p.promise_responses
       *self->a1: propose(p.proposal, p.value);
       a1->self*: accept)

  $ protocol print paxos.spec --party P:p:a,p,proposal,value,majority,promise_responses,cp,cv: --party L:l:: --party A:a,a1:p,highest_proposal,accepted_proposal,accepted_value,n,pn,pv: --project L
  (forall p in P
     forall a1 in p.promise_responses
       a1->self*: accept)

  $ protocol print paxos.spec --party P:p:a,p,proposal,value,majority,promise_responses,cp,cv: --party L:l:: --party A:a,a1:p,highest_proposal,accepted_proposal,accepted_value,n,pn,pv: --project A
  a.highest_proposal = [0, 0];
  a.accepted_proposal = [0, 0];
  a.accepted_value = 0;
  (forall p in P
     p->self*: prepare(n);
     (n > a.highest_proposal =>
        a.highest_proposal = n;
        *self->p: promise(a.accepted_proposal, a.accepted_value))
     ||
     p->self*: propose(pn, pv);
     (pn == a1.highest_proposal =>
        a1.accepted_proposal = pn;
        a1.accepted_value = pv;
        *self->p: accept;
        (forall l in L
           *self->l: accept)))

  $ protocol print --ast paxos.spec
  (Seq
     [(Forall (p, P,
         (Seq
            [(Assign (p.proposal, 0)); (Assign (p.value, external()));
              (Assign (p.cp, [0, 0])); (Assign (p.majority, size(A) / 2 + 1));
              (Assign (p.promise_responses, {}))])
         ));
       (Forall (a, A,
          (Seq
             [(Assign (a.highest_proposal, [0, 0]));
               (Assign (a.accepted_proposal, [0, 0]));
               (Assign (a.accepted_value, 0))])
          ));
       (Forall (p, P,
          (Par
             [(Seq
                 [(Assign (p.proposal, p.proposal + 1));
                   (Forall (a, A,
                      (Seq
                         [Send {from = p; to_ = a;
                            msg = prepare(n=[p,
  p.proposal])};
                           (Imply (n > a.highest_proposal,
                              (Seq
                                 [(Assign (a.highest_proposal, n));
                                   Send {from = a; to_ = p;
                                     msg =
                                     promise(cp=a.accepted_proposal, cv=a.accepted_value)};
                                   (Assign (p.promise_responses,
                                      p.promise_responses + {a}));
                                   (Imply (cp > [0, 0] & cp > p.cp,
                                      (Seq
                                         [(Assign (p.cp, cp));
                                           (Assign (p.value, cv))])
                                      ))
                                   ])
                              ))
                           ])
                      ))
                   ]);
               (BlockingImply (size(p.promise_responses) > p.majority,
                  (Forall (a1, p.promise_responses,
                     (Seq
                        [Send {from = p; to_ = a1;
                           msg = propose(pn=p.proposal, pv=p.value)};
                          (Imply (pn == a1.highest_proposal,
                             (Seq
                                [(Assign (a1.accepted_proposal, pn));
                                  (Assign (a1.accepted_value, pv));
                                  Send {from = a1; to_ = p; msg = accept};
                                  (Forall (l, L,
                                     Send {from = a1; to_ = l; msg = accept}))
                                  ])
                             ))
                          ])
                     ))
                  ))
               ])
          ))
       ])
