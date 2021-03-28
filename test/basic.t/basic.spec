  a.b = 1;
  b.c = 2;
  c.d = 3
||
  a.b = {1}
||
  // lol
  a.b = [1] // haha
||
  a.b = f(a, 1, 2)
||
  a.b = {a: 1}
||
  s->r: m(a = 1, b = 2)
||
  1 => a.b = 1; b.c = 2
||
  forall a in b a.b = 1; c.a = 2 \/ a.a = 1