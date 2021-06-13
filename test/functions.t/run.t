Incomplete recursion example

  $ protocol print fns.spec --parties P,C --project P --actions
  digraph G {
    1 [label="PReceiveM1\ntid: Pt0(c:C)\n{start}\nthis: {Pt0(c:C) = 1}\nparams: [(c:C)]\nc->: m"];
    2 [label="PAction2\ntid: Pmain\n{∀ c:C. Pt0(c:C) = 1}\nthis: {Pmain = 2}\nskip"];
    3 [label="PChangeA3\ntid: Pt2(p:P)\n{Pmain = 2}\nthis: {Pt2(p:P) = 3}\np.a = 1"];
    4 [label="PChangeB4\ntid: Pt0(p:P)\n{Pmain = 2}\nthis: {Pt0(p:P) = 4}\np.b = 2"];
    5 [label="PChangeC5\ntid: Pt1(p:P)\n{∀ p:P. Pt0(p:P) = 4}\nthis: {Pt1(p:P) = 5}\np.c = 3"];
    4 -> 5;
    3 -> 2;
    2 -> 4;
    2 -> 3;
    1 -> 2;
  }
