Examples to stress-test the parser.

  $ protocol print --no-normalize basic.spec
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
    a.a = a & (b | c)

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
    a.a = a & (b | c)

  $ protocol print basic.spec > basic1.spec && protocol print basic1.spec | protocol print > basic2.spec && git diff --no-index basic1.spec basic2.spec
