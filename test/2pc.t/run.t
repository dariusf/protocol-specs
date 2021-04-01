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

  $ protocol print 2pc.spec --party C:c:responded,aborted,p: --party P:p:c: --project C
  forall p in P
    *self->p: prepare;
        p->self*: prepared;
        responded = responded + {p}
      \/
        p->self*: abort;
        aborted = aborted + {p}
    ;
    aborted == {} =>*
        forall p in P
          *self->p: commit;
          p->self*: commit_ack
      \/
        forall p in P
          *self->p: abort;
          p->self*: abort_ack

  $ protocol print 2pc.spec --party C:c:responded,aborted,p: --party P:p:c: --project P
  forall c in C
    c->self*: prepare;
        *self->c: prepared
      \/
        *self->c: abort
    ;
      c->self*: commit;
      *self->c: commit_ack
    \/
      c->self*: abort;
      *self->c: abort_ack

  $ protocol print --ast 2pc.spec