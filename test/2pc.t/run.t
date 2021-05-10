The classic two-phase commit protocol.

  $ protocol print 2pc.spec
  forall c in C
    (forall p in P
       c->p: prepare;
       (p->c: prepared;
        responded = union(responded, {p})
        \/
        p->c: abort;
        aborted = union(aborted, {p})));
    (aborted == {} =>*
       (forall p in P
          c->p: commit;
          p->c: commit_ack
        \/
        forall p in P
          c->p: abort;
          p->c: abort_ack))

  $ protocol print --parties P,C --types 2pc.spec
  forall (c : party C;global) in (C : {party C};global)
    (forall (p : party P;global) in (P : {party P};global)
       (c : party C;global)->(p : party P;global): prepare;
       ((p : party P;P)->(c : party C;P): prepared;
        (responded : {party P};C) = union((responded : {party P};C), {(p : party P;C)})
        \/
        (p : party P;P)->(c : party C;P): abort;
        (aborted : {party P};C) = union((aborted : {party P};C), {(p : party P;C)})));
    ((aborted : {party P};C) == {} =>*
       (forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global): commit;
          (p : party P;P)->(c : party C;P): commit_ack
        \/
        forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global): abort;
          (p : party P;P)->(c : party C;P): abort_ack))

  $ protocol print 2pc.spec --parties C,P --project C
  (forall p in P
     *self->p: prepare;
     (p->self*: prepared;
      responded = union(responded, {p})
      \/
      p->self*: abort;
      aborted = union(aborted, {p})));
  (aborted == {} =>*
     (forall p in P
        *self->p: commit;
        p->self*: commit_ack
      \/
      forall p in P
        *self->p: abort;
        p->self*: abort_ack))

  $ protocol print 2pc.spec --parties C,P --project P
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

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && git diff --no-index 2pc1.spec 2pc2.spec
