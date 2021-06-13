Incomplete recursion example

  $ protocol print fns.spec --parties P,C --project P --actions
  digraph G {
    1 [label="PReceiveM1\ntid: Pt0(c:C)\n{start}\nλ [(c:C)].\nc->: m"];
    2 [label="PAction2\ntid: main\n{∀ c:C. Pt0(c:C) = 1}\nskip"];
    3 [label="PChangeA3\ntid: main\n{start}\np.a = 1"];
    4 [label="PChangeD4\ntid: main\n{∀ p:P. main = 3}\np.d = 1"];
    5 [label="PChangeB5\ntid: main\n{start}\np.b = 2"];
    6 [label="PChangeC6\ntid: main\n{∀ p:P. main = 5}\np.c = 3"];
    5 -> 6;
    4 -> 2;
    3 -> 4;
    2 -> 5;
    2 -> 3;
    1 -> 2;
  }
