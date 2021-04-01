The classic two-phase commit protocol.

  $ protocol print 2pc.spec
  forall c in C
    (forall p in P
       c->p: prepare;
       (p->c: prepared;
        responded = responded + {p}
        \/
        p->c: abort;
        aborted = aborted + {p}));
    (aborted == {} =>*
       (forall p in P
          c->p: commit;
          p->c: commit_ack
        \/
        forall p in P
          c->p: abort;
          p->c: abort_ack))

  $ protocol print 2pc.spec --party C:c:responded,aborted,p: --party P:p:c: --project C
  (forall p in P
     *self->p: prepare;
     (p->self*: prepared;
      responded = responded + {p}
      \/
      p->self*: abort;
      aborted = aborted + {p}));
  (aborted == {} =>*
     (forall p in P
        *self->p: commit;
        p->self*: commit_ack
      \/
      forall p in P
        *self->p: abort;
        p->self*: abort_ack))

  $ protocol print 2pc.spec --party C:c:responded,aborted,p: --party P:p:c: --project P
  forall c in C
    c->self*: prepare;
    (*self->c: prepared
     \/
     *self->c: abort);
    (c->self*: commit;
     *self->c: commit_ack
     \/
     c->self*: abort;
     *self->c: abort_ack)

  $ protocol print --ast 2pc.spec
  (Forall (c, C,
     (Seq
        [(Forall (p, P,
            (Seq
               [Send {from = c; to_ = p; msg = prepare};
                 (Disj (
                    (Seq
                       [Send {from = p; to_ = c; msg = prepared};
                         (Assign (responded,
                            (App ("+", [(Var responded); (Set [(Var p)])]))))
                         ]),
                    (Seq
                       [Send {from = p; to_ = c; msg = abort};
                         (Assign (aborted,
                            (App ("+", [(Var aborted); (Set [(Var p)])]))))
                         ])
                    ))
                 ])
            ));
          (BlockingImply ((App ("==", [(Var aborted); (Set [])])),
             (Disj (
                (Forall (p, P,
                   (Seq
                      [Send {from = c; to_ = p; msg = commit};
                        Send {from = p; to_ = c; msg = commit_ack}])
                   )),
                (Forall (p, P,
                   (Seq
                      [Send {from = c; to_ = p; msg = abort};
                        Send {from = p; to_ = c; msg = abort_ack}])
                   ))
                ))
             ))
          ])
     ))

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && git diff --no-index 2pc1.spec 2pc2.spec
