Examples to stress-test the parser.

  $ protocol print <<EOF
  > a.b = 1;
  > b.c = 1
  > EOF
  a.b = 1;
  b.c = 1

  $ protocol print <<EOF
  > (a.b = 1 || a.d = 2); b.c = 1
  > EOF
  (a.b = 1
   ||
   a.d = 2);
  b.c = 1

  $ protocol print <<EOF
  > (a.b = 1 \/ a.d = 2); b.c = 1
  > EOF
  (a.b = 1
   \/
   a.d = 2);
  b.c = 1

  $ protocol print <<EOF
  > a.b = 1 \/ a.d = 2 || b.c = 1
  > EOF
  a.b = 1
  \/
  a.d = 2
  ||
  b.c = 1

  $ protocol print <<EOF
  > a.b = 1 || a.d = 2 \/ b.c = 1
  > EOF
  a.b = 1
  ||
  a.d = 2
  \/
  b.c = 1

  $ protocol print <<EOF
  > (forall a in A b.b = 2); a.a = 1
  > EOF
  (forall a in A
     b.b = 2);
  a.a = 1

  $ protocol print <<EOF
  > forall a in A b.b = 2; b.c = 3 \/ a.a = 1; b.b = 2
  > EOF
  forall a in A
    b.b = 2;
    b.c = 3
  \/
  a.a = 1;
  b.b = 2

  $ protocol print <<EOF
  > a => b.b = 2; b.c = 3
  > EOF
  a =>
    b.b = 2;
    b.c = 3

Note that the parens are only added when necessary.

  $ protocol print <<EOF
  > b.c = 3; a => b.b = 2
  > EOF
  b.c = 3;
  (a =>
     b.b = 2)

  $ protocol print <<EOF
  > (a => b.b = 2); b.c = 3
  > EOF
  (a =>
     b.b = 2);
  b.c = 3

  $ protocol print <<EOF
  > a => b.b = 2 || b.c = 3
  > EOF
  a =>
    b.b = 2
  ||
  b.c = 3

  $ protocol print <<EOF
  > a => b.b = 2 \/ c => b.c = 3
  > EOF
  a =>
    b.b = 2
  \/
  c =>
    b.c = 3

  $ protocol print basic.spec
  a.b = 1;
  b.c = 2;
  c.d = 3
  ||
  a.b = {1}
  ||
  a.b = [1]
  ||
  a.b = f(a, 1, 2)
  ||
  a.b = {a: 1}
  ||
  s->r: m(a=1, b=2)
  ||
  1 =>
    a.b = 1;
    b.c = 2
  ||
  forall a in b
    a.b = 1;
    c.a = 2
  \/
  a.a = 1
  ||
  (a.a = 1
   ||
   a.b = 2);
  a.c = 3
  ||
  (a.a = 1
   \/
   a.b = 2);
  a.c = 3
  ||
  (forall a in b
     a.b = 1;
     c.a = 2);
  a.a = 1
  ||
  a.a = a & (b | c)

  $ protocol print --ast basic.spec
  (Par
     [(Disj (
         (Par
            [(Seq
                [(Assign (a.b, (Int 1))); (Assign (b.c, (Int 2)));
                  (Assign (c.d, (Int 3)))]);
              (Assign (a.b, (Set [(Int 1)])));
              (Assign (a.b, (List [(Int 1)])));
              (Assign (a.b, (App ("f", [(Var a); (Int 1); (Int 2)]))));
              (Assign (a.b, (Map [("a", (Int 1))])));
              Send {from = s; to_ = r; msg = m(a=(Int 1), b=(Int 2))};
              (Imply ((Int 1),
                 (Seq [(Assign (a.b, (Int 1))); (Assign (b.c, (Int 2)))])));
              (Forall (a, b,
                 (Seq [(Assign (a.b, (Int 1))); (Assign (c.a, (Int 2)))])))
              ]),
         (Assign (a.a, (Int 1)))));
       (Seq
          [(Par [(Assign (a.a, (Int 1))); (Assign (a.b, (Int 2)))]);
            (Assign (a.c, (Int 3)))]);
       (Seq
          [(Disj ((Assign (a.a, (Int 1))), (Assign (a.b, (Int 2)))));
            (Assign (a.c, (Int 3)))]);
       (Seq
          [(Forall (a, b,
              (Seq [(Assign (a.b, (Int 1))); (Assign (c.a, (Int 2)))])));
            (Assign (a.a, (Int 1)))]);
       (Assign (a.a, (App ("&", [(Var a); (App ("|", [(Var b); (Var c)]))]))))])

  $ protocol print basic.spec > basic1.spec && protocol print basic1.spec | protocol print > basic2.spec && git diff --no-index basic1.spec basic2.spec
