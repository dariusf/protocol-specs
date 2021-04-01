The classic two-phase commit protocol.

  $ protocol print 2pc.spec
  forall c in C
    forall p in P
      c->p: prepare;
          p->c: prepared;
          responded = responded + {p}
        \/
          p->c: abort;
          aborted = aborted + {p}
      ;
      aborted == {} =>*
          forall p in P
            c->p: commit;
            p->c: commit_ack
        \/
          forall p in P
            c->p: abort;
            p->c: abort_ack

  $ protocol print 2pc.spec --party C:c:responded,aborted,p --party P:p:c
  parties [{ repr = C; other_sets = []; vars = [c];
     owned_vars = [responded; aborted; p] };
    { repr = P; other_sets = []; vars = [p]; owned_vars = [c] }]
