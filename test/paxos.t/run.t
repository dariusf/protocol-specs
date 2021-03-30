Simplest possible cram test

  $ protocol print paxos.spec
    forall p in P.
      p.proposal = 0;
      p.value = external();
      p.cp = [0, 0];
      p.majority = size(A) / 2 + 1;
      p.promise_responses = {};
      forall a in A.
        a.highest_proposal = [0, 0];
        a.accepted_proposal = [0, 0];
        a.accepted_value = 0;
        forall p in P.
          p.proposal = p.proposal + 1;
          forall a in A.
            p->a: prepare(n=[p, p.proposal]);
            n > a.highest_proposal =>
              a.highest_proposal = n;
              a->p: promise(cp=a.accepted_proposal, cv=a.accepted_value);
              p.promise_responses = p.promise_responses + {a};
              cp > [0, 0] & cp > p.cp =>
                p.cp = cp;
                p.value = cv
  ||
    size(p.promise_responses) > p.majority =>*
      forall a1 in p.promise_responses.
        p->a1: propose(pn=p.proposal, pv=p.value);
        pn == a1.highest_proposal =>
          a1.accepted_proposal = pn;
          a1.accepted_value = pv;
          a1->p: accept;
          forall l in L.
            a1->l: accept
  ---
    forall p in P.
      p.proposal = 0;
      p.value = external();
      p.cp = [0, 0];
      p.majority = size(A) / 2 + 1;
      p.promise_responses = {};
      forall a in A.
        a.highest_proposal = [0, 0];
        a.accepted_proposal = [0, 0];
        a.accepted_value = 0;
        forall p in P.
          p.proposal = p.proposal + 1;
          forall a in A.
            p->a: prepare(n=[p, p.proposal]);
            n > a.highest_proposal =>
              a.highest_proposal = n;
              a->p: promise(cp=a.accepted_proposal, cv=a.accepted_value);
              p.promise_responses = p.promise_responses + {a};
              cp > [0, 0] & cp > p.cp =>
                p.cp = cp;
                p.value = cv
  ||
    size(p.promise_responses) > p.majority =>*
      forall a1 in p.promise_responses.
        p->a1: propose(pn=p.proposal, pv=p.value);
        pn == a1.highest_proposal =>
          a1.accepted_proposal = pn;
          a1.accepted_value = pv;
          a1->p: accept;
          forall l in L.
            a1->l: accept
  ---
  (Ast.Par
     [(Ast.Forall (p, P,
         (Ast.Seq
            [(Ast.Assign (p.proposal, 0)); (Ast.Assign (p.value, external()));
              (Ast.Assign (p.cp, [0, 0]));
              (Ast.Assign (p.majority, size(A) / 2 + 1));
              (Ast.Assign (p.promise_responses, {}));
              (Ast.Forall (a, A,
                 (Ast.Seq
                    [(Ast.Assign (a.highest_proposal, [0, 0]));
                      (Ast.Assign (a.accepted_proposal, [0, 0]));
                      (Ast.Assign (a.accepted_value, 0));
                      (Ast.Forall (p, P,
                         (Ast.Seq
                            [(Ast.Assign (p.proposal, p.proposal + 1));
                              (Ast.Forall (a, A,
                                 (Ast.Seq
                                    [Ast.Send {from = p; to_ = a;
                                       msg = prepare(n=[p,
  p.proposal])};
                                      (Ast.Imply (n > a.highest_proposal,
                                         (Ast.Seq
                                            [(Ast.Assign (a.highest_proposal, n
                                                ));
                                              Ast.Send {from = a; to_ = p;
                                                msg =
                                                promise(cp=a.accepted_proposal, cv=a.accepted_value)};
                                              (Ast.Assign (p.promise_responses,
                                                 p.promise_responses + {a}));
                                              (Ast.Imply (
                                                 cp > [0, 0] & cp > p.cp,
                                                 (Ast.Seq
                                                    [(Ast.Assign (p.cp, cp));
                                                      (Ast.Assign (p.value, cv
                                                         ))
                                                      ])
                                                 ))
                                              ])
                                         ))
                                      ])
                                 ))
                              ])
                         ))
                      ])
                 ))
              ])
         ));
       (Ast.BlockingImply (size(p.promise_responses) > p.majority,
          (Ast.Forall (a1, p.promise_responses,
             (Ast.Seq
                [Ast.Send {from = p; to_ = a1;
                   msg = propose(pn=p.proposal, pv=p.value)};
                  (Ast.Imply (pn == a1.highest_proposal,
                     (Ast.Seq
                        [(Ast.Assign (a1.accepted_proposal, pn));
                          (Ast.Assign (a1.accepted_value, pv));
                          Ast.Send {from = a1; to_ = p; msg = accept};
                          (Ast.Forall (l, L,
                             Ast.Send {from = a1; to_ = l; msg = accept}))
                          ])
                     ))
                  ])
             ))
          ))
       ])
  
