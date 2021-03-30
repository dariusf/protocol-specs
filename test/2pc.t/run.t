Simplest possible cram test

  $ protocol print 2pc.spec
  forall c in C.
      forall p in P.
        c->p: prepare;
          p->c: prepared;
          responded = responded + {p}
        \/
          p->c: abort;
          aborted = aborted + {p};
        aborted == {} =>*
          forall p in P.
            c->p: commit;
            p->c: commit_ack
    \/
      forall p in P.
        c->p: abort;
        p->c: abort_ack
  ---
  forall c in C.
      forall p in P.
        c->p: prepare;
          p->c: prepared;
          responded = responded + {p}
        \/
          p->c: abort;
          aborted = aborted + {p};
        aborted == {} =>*
          forall p in P.
            c->p: commit;
            p->c: commit_ack
    \/
      forall p in P.
        c->p: abort;
        p->c: abort_ack
  ---
  (Ast.Forall (c, C,
     (Ast.Disj (
        (Ast.Forall (p, P,
           (Ast.Seq
              [Ast.Send {from = c; to_ = p; msg = prepare};
                (Ast.Disj (
                   (Ast.Seq
                      [Ast.Send {from = p; to_ = c; msg = prepared};
                        (Ast.Assign (responded, responded + {p}))]),
                   (Ast.Seq
                      [Ast.Send {from = p; to_ = c; msg = abort};
                        (Ast.Assign (aborted, aborted + {p}))])
                   ));
                (Ast.BlockingImply (aborted == {},
                   (Ast.Forall (p, P,
                      (Ast.Seq
                         [Ast.Send {from = c; to_ = p; msg = commit};
                           Ast.Send {from = p; to_ = c; msg = commit_ack}])
                      ))
                   ))
                ])
           )),
        (Ast.Forall (p, P,
           (Ast.Seq
              [Ast.Send {from = c; to_ = p; msg = abort};
                Ast.Send {from = p; to_ = c; msg = abort_ack}])
           ))
        ))
     ))
  
  $ protocol print 2pc.spec --party C:c:responded,aborted,p --party P:p:c
  parties [{ repr = C; other_sets = []; vars = [c];
     owned_vars = [responded; aborted; p] };
    { repr = P; other_sets = []; vars = [p]; owned_vars = [c] }]
