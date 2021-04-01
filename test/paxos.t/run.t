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
            [(Assign (p.proposal, (Int 0)));
              (Assign (p.value, (App ("external", []))));
              (Assign (p.cp, (List [(Int 0); (Int 0)])));
              (Assign (p.majority,
                 (App ("+",
                    [(App ("/", [(App ("size", [(Var A)])); (Int 2)])); (
                      Int 1)]
                    ))
                 ));
              (Assign (p.promise_responses, (Set [])))])
         ));
       (Forall (a, A,
          (Seq
             [(Assign (a.highest_proposal, (List [(Int 0); (Int 0)])));
               (Assign (a.accepted_proposal, (List [(Int 0); (Int 0)])));
               (Assign (a.accepted_value, (Int 0)))])
          ));
       (Forall (p, P,
          (Par
             [(Seq
                 [(Assign (p.proposal, (App ("+", [(Var p.proposal); (Int 1)]))
                     ));
                   (Forall (a, A,
                      (Seq
                         [Send {from = p; to_ = a;
                            msg = prepare(n=(List [(Var p); (Var p.proposal)]))};
                           (Imply (
                              (App (">", [(Var n); (Var a.highest_proposal)])),
                              (Seq
                                 [(Assign (a.highest_proposal, (Var n)));
                                   Send {from = a; to_ = p;
                                     msg =
                                     promise(cp=(Var a.accepted_proposal), cv=(Var a.accepted_value))};
                                   (Assign (p.promise_responses,
                                      (App ("+",
                                         [(Var p.promise_responses);
                                           (Set [(Var a)])]
                                         ))
                                      ));
                                   (Imply (
                                      (App (">",
                                         [(App (">",
                                             [(Var cp);
                                               (App ("&",
                                                  [(List [(Int 0); (Int 0)]);
                                                    (Var cp)]
                                                  ))
                                               ]
                                             ));
                                           (Var p.cp)]
                                         )),
                                      (Seq
                                         [(Assign (p.cp, (Var cp)));
                                           (Assign (p.value, (Var cv)))])
                                      ))
                                   ])
                              ))
                           ])
                      ))
                   ]);
               (BlockingImply (
                  (App (">",
                     [(App ("size", [(Var p.promise_responses)]));
                       (Var p.majority)]
                     )),
                  (Forall (a1, p.promise_responses,
                     (Seq
                        [Send {from = p; to_ = a1;
                           msg = propose(pn=(Var p.proposal), pv=(Var p.value))};
                          (Imply (
                             (App ("==", [(Var pn); (Var a1.highest_proposal)]
                                )),
                             (Seq
                                [(Assign (a1.accepted_proposal, (Var pn)));
                                  (Assign (a1.accepted_value, (Var pv)));
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
