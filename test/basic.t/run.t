Simplest possible cram test

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
        forall a in b.
          a.b = 1;
          c.a = 2
      \/
        a.a = 1
  ||
    a.a = a & (b | c)
  ---
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
      forall a in b.
        a.b = 1;
        c.a = 2
    \/
      a.a = 1
  ||
    a.a = a & (b | c)
  ---
  (Ast.Par
     [(Ast.Seq
         [(Ast.Assign (a.b, 1)); (Ast.Assign (b.c, 2)); (Ast.Assign (c.d, 3))]);
       (Ast.Assign (a.b, {1})); (Ast.Assign (a.b, [1]));
       (Ast.Assign (a.b, f(a, 1, 2))); (Ast.Assign (a.b, {a: 1}));
       Ast.Send {from = s; to_ = r; msg = m(a=1, b=2)};
       (Ast.Imply (1, (Ast.Seq [(Ast.Assign (a.b, 1)); (Ast.Assign (b.c, 2))])
          ));
       (Ast.Disj (
          (Ast.Forall (a, b,
             (Ast.Seq [(Ast.Assign (a.b, 1)); (Ast.Assign (c.a, 2))]))),
          (Ast.Assign (a.a, 1))));
       (Ast.Assign (a.a, a & b | c))])
  
