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
    (aborted == {} =>
       (forall p in P
          c->p: commit;
          p->c: commit_ack)
     \/
     aborted != {} =>
       (forall p in P
          c->p: abort;
          p->c: abort_ack))

  $ protocol print 2pc-wait.spec
  forall c in C
    forall p in P
      c->p: prepare;
      (p->c: prepared;
       responded = union(responded, {p})
       \/
       p->c: abort;
       aborted = union(aborted, {p}))
  ||
  responded == P =>*
    (forall p in P
       c->p: commit;
       p->c: commit_ack)
  \/
  aborted != {} =>*
    (forall p in P
       c->p: abort;
       p->c: abort_ack)

  $ protocol print --parties P,C --types 2pc.spec
  forall (c : party C;global) in (C : {party C};global)
    (forall (p : party P;global) in (P : {party P};global)
       (c : party C;global)->(p : party P;global): prepare;
       ((p : party P;P)->(c : party C;P): prepared;
        (responded : {party P};C) = union((responded : {party P};C), {(p : party P;C)})
        \/
        (p : party P;P)->(c : party C;P): abort;
        (aborted : {party P};C) = union((aborted : {party P};C), {(p : party P;C)})));
    ((aborted : {party P};C) == {} =>
       (forall (p : party P;global) in (P : {party P};global)
          (c : party C;global)->(p : party P;global): commit;
          (p : party P;P)->(c : party C;P): commit_ack)
     \/
     (aborted : {party P};C) != {} =>
       (forall (p : party P;global) in (P : {party P};global)
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
  (aborted == {} =>
     (forall p in P
        *self->p: commit;
        p->self*: commit_ack)
   \/
   aborted != {} =>
     (forall p in P
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

  $ protocol print 2pc.spec --parties C,P --project P --actions
  digraph G {
    0 [label="λ c.\nc->self*: prepare"];
    1 [label="λ c.\n*self->c: prepared"];
    2 [label="λ c.\n*self->c: abort"];
    3 [label="λ c.\nc->self*: commit"];
    4 [label="λ c.\n*self->c: commit_ack"];
    5 [label="λ c.\nc->self*: abort"];
    6 [label="λ c.\n*self->c: abort_ack"];
    5 -> 6;
    3 -> 4;
    2 -> 5;
    2 -> 3;
    1 -> 5;
    1 -> 3;
    0 -> 2;
    0 -> 1;
  }

  $ protocol print 2pc.spec --parties C,P --project C --actions
  digraph G {
    0 [label="λ p.\n*self->p: prepare"];
    1 [label="λ p.\np->self*: prepared;\nresponded = union(responded, {p})"];
    2 [label="λ p.\np->self*: abort;\naborted = union(aborted, {p})"];
    3 [label="{aborted == {}}\nλ p.\n*self->p: commit"];
    4 [label="{aborted == {}}\nλ p.\np->self*: commit_ack"];
    5 [label="{aborted != {}}\nλ p.\n*self->p: abort"];
    6 [label="{aborted != {}}\nλ p.\np->self*: abort_ack"];
    5 -> 6;
    3 -> 4;
    2 -> 5;
    2 -> 3;
    1 -> 5;
    1 -> 3;
    0 -> 2;
    0 -> 1;
  }

  $ protocol print 2pc.spec > 2pc1.spec && protocol print 2pc1.spec | protocol print > 2pc2.spec && git diff --no-index 2pc1.spec 2pc2.spec

  $ protocol print 2pc-wait.spec > 2pc1-wait.spec && protocol print 2pc1-wait.spec | protocol print > 2pc2-wait.spec && git diff --no-index 2pc1-wait.spec 2pc2-wait.spec
