Non-blocking atomic commitment

  $ protocol print nbac.spec --project P
  forall f in F
    (f-> : exception(id);
     some_failed = true
     \/
     f-> : ok)
  ||
  ->self : yes;
  self-> : yes;
  voted_yes = union(voted_yes, {self})
  \/
  ->self : no;
  self-> : no;
  no = true
  ||
  forall q in (P \ {self})
    (->q : yes
     \/
     ->q : no)
  ||
  forall p in (P \ {self})
    (p-> : yes;
     voted_yes = union(voted_yes, {p})
     \/
     p-> : no;
     no = true)
  ||
  no | some_failed =>*
    outcome = 'abort'
  \/
  voted_yes == P =>*
    outcome = 'commit'

  $ protocol print nbac.spec --project F
  forall p in P
    (->p : exception(id=p)
     \/
     ->p : ok)

  $ protocol print nbac.spec > nbac1.spec && protocol print nbac1.spec | protocol print > nbac2.spec && diff -uw nbac1.spec nbac2.spec
