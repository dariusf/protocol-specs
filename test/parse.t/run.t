These two have the same precedence and associativity.

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

Low-precedence expressions in a higher-precedence context should remain parenthesized.

  $ protocol print <<EOF
  > (a.b = 1 || a.d = 2); b.c = 1
  > EOF
  (a.b = 1
   ||
   a.d = 2);
  b.c = 1

  $ protocol print <<EOF
  > b.c = 1; (a.b = 1 || a.d = 2)
  > EOF
  b.c = 1;
  (a.b = 1
   ||
   a.d = 2)

  $ protocol print <<EOF
  > (a.b = 1 \/ a.d = 2); b.c = 1
  > EOF
  (a.b = 1
   \/
   a.d = 2);
  b.c = 1

  $ protocol print <<EOF
  > b.c = 1; (a.b = 1 \/ a.d = 2)
  > EOF
  b.c = 1;
  (a.b = 1
   \/
   a.d = 2)

  $ protocol print <<EOF
  > (forall a in A b.b = 2); a.a = 1
  > EOF
  (forall a in A
     b.b = 2);
  a.a = 1

  $ protocol print <<EOF
  > forall a in A (b.b = 2 || a.a = 1)
  > EOF
  forall a in A
    (b.b = 2
     ||
     a.a = 1)

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

  $ protocol print parse.spec
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
  s->r : m(a=1, b=2)
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
  a.a = d & a & (b | c)

  $ protocol print --ast parse.spec
  { decls = [];
    protocol =
    { pmeta = { start = { line = 1; col = 2 }; stop = { line = 26; col = 23 } };
      p =
      (Par
         [{ pmeta =
            { start = { line = 1; col = 2 }; stop = { line = 18; col = 43 } };
            p =
            (Disj (
               { pmeta =
                 { start = { line = 1; col = 2 };
                   stop = { line = 18; col = 32 } };
                 p =
                 (Par
                    [{ pmeta =
                       { start = { line = 1; col = 2 };
                         stop = { line = 3; col = 9 } };
                       p =
                       (Seq
                          [{ pmeta =
                             { start = { line = 1; col = 2 };
                               stop = { line = 1; col = 9 } };
                             p =
                             (Assign (
                                { meta =
                                  { start = { line = 1; col = 2 };
                                    stop = { line = 1; col = 5 } };
                                  expr = (Var a.b) },
                                { meta =
                                  { start = { line = 1; col = 8 };
                                    stop = { line = 1; col = 9 } };
                                  expr = (Int 1) }
                                ))
                             };
                            { pmeta =
                              { start = { line = 2; col = 2 };
                                stop = { line = 2; col = 9 } };
                              p =
                              (Assign (
                                 { meta =
                                   { start = { line = 2; col = 2 };
                                     stop = { line = 2; col = 5 } };
                                   expr = (Var b.c) },
                                 { meta =
                                   { start = { line = 2; col = 8 };
                                     stop = { line = 2; col = 9 } };
                                   expr = (Int 2) }
                                 ))
                              };
                            { pmeta =
                              { start = { line = 3; col = 2 };
                                stop = { line = 3; col = 9 } };
                              p =
                              (Assign (
                                 { meta =
                                   { start = { line = 3; col = 2 };
                                     stop = { line = 3; col = 5 } };
                                   expr = (Var c.d) },
                                 { meta =
                                   { start = { line = 3; col = 8 };
                                     stop = { line = 3; col = 9 } };
                                   expr = (Int 3) }
                                 ))
                              }
                            ])
                       };
                      { pmeta =
                        { start = { line = 5; col = 2 };
                          stop = { line = 5; col = 11 } };
                        p =
                        (Assign (
                           { meta =
                             { start = { line = 5; col = 2 };
                               stop = { line = 5; col = 5 } };
                             expr = (Var a.b) },
                           { meta =
                             { start = { line = 5; col = 8 };
                               stop = { line = 5; col = 11 } };
                             expr =
                             (Set
                                [{ meta =
                                   { start = { line = 5; col = 9 };
                                     stop = { line = 5; col = 10 } };
                                   expr = (Int 1) }
                                  ])
                             }
                           ))
                        };
                      { pmeta =
                        { start = { line = 8; col = 2 };
                          stop = { line = 8; col = 11 } };
                        p =
                        (Assign (
                           { meta =
                             { start = { line = 8; col = 2 };
                               stop = { line = 8; col = 5 } };
                             expr = (Var a.b) },
                           { meta =
                             { start = { line = 8; col = 8 };
                               stop = { line = 8; col = 11 } };
                             expr =
                             (List
                                [{ meta =
                                   { start = { line = 8; col = 9 };
                                     stop = { line = 8; col = 10 } };
                                   expr = (Int 1) }
                                  ])
                             }
                           ))
                        };
                      { pmeta =
                        { start = { line = 10; col = 2 };
                          stop = { line = 10; col = 18 } };
                        p =
                        (Assign (
                           { meta =
                             { start = { line = 10; col = 2 };
                               stop = { line = 10; col = 5 } };
                             expr = (Var a.b) },
                           { meta =
                             { start = { line = 10; col = 8 };
                               stop = { line = 10; col = 18 } };
                             expr =
                             (App ("f",
                                [{ meta =
                                   { start = { line = 10; col = 10 };
                                     stop = { line = 10; col = 11 } };
                                   expr = (Var a) };
                                  { meta =
                                    { start = { line = 10; col = 13 };
                                      stop = { line = 10; col = 14 } };
                                    expr = (Int 1) };
                                  { meta =
                                    { start = { line = 10; col = 16 };
                                      stop = { line = 10; col = 17 } };
                                    expr = (Int 2) }
                                  ]
                                ))
                             }
                           ))
                        };
                      { pmeta =
                        { start = { line = 12; col = 2 };
                          stop = { line = 12; col = 14 } };
                        p =
                        (Assign (
                           { meta =
                             { start = { line = 12; col = 2 };
                               stop = { line = 12; col = 5 } };
                             expr = (Var a.b) },
                           { meta =
                             { start = { line = 12; col = 8 };
                               stop = { line = 12; col = 14 } };
                             expr =
                             (Map
                                [("a",
                                  { meta =
                                    { start = { line = 12; col = 12 };
                                      stop = { line = 12; col = 13 } };
                                    expr = (Int 1) })
                                  ])
                             }
                           ))
                        };
                      { pmeta =
                        { start = { line = 14; col = 2 };
                          stop = { line = 14; col = 23 } };
                        p =
                        Send {
                          from =
                          { meta =
                            { start = { line = 14; col = 2 };
                              stop = { line = 14; col = 3 } };
                            expr = (Var s) };
                          to_ =
                          { meta =
                            { start = { line = 14; col = 5 };
                              stop = { line = 14; col = 6 } };
                            expr = (Var r) };
                          msg =
                          Message {typ = "m";
                            args =
                            [({ meta =
                                { start = { line = 14; col = 10 };
                                  stop = { line = 14; col = 11 } };
                                expr = (Var a) },
                              { meta =
                                { start = { line = 14; col = 14 };
                                  stop = { line = 14; col = 15 } };
                                expr = (Int 1) });
                              ({ meta =
                                 { start = { line = 14; col = 17 };
                                   stop = { line = 14; col = 18 } };
                                 expr = (Var b) },
                               { meta =
                                 { start = { line = 14; col = 21 };
                                   stop = { line = 14; col = 22 } };
                                 expr = (Int 2) })
                              ]}}
                        };
                      { pmeta =
                        { start = { line = 16; col = 2 };
                          stop = { line = 16; col = 23 } };
                        p =
                        (Imply (
                           { meta =
                             { start = { line = 16; col = 2 };
                               stop = { line = 16; col = 3 } };
                             expr = (Int 1) },
                           { pmeta =
                             { start = { line = 16; col = 7 };
                               stop = { line = 16; col = 23 } };
                             p =
                             (Seq
                                [{ pmeta =
                                   { start = { line = 16; col = 7 };
                                     stop = { line = 16; col = 14 } };
                                   p =
                                   (Assign (
                                      { meta =
                                        { start = { line = 16; col = 7 };
                                          stop = { line = 16; col = 10 } };
                                        expr = (Var a.b) },
                                      { meta =
                                        { start = { line = 16; col = 13 };
                                          stop = { line = 16; col = 14 } };
                                        expr = (Int 1) }
                                      ))
                                   };
                                  { pmeta =
                                    { start = { line = 16; col = 16 };
                                      stop = { line = 16; col = 23 } };
                                    p =
                                    (Assign (
                                       { meta =
                                         { start = { line = 16; col = 16 };
                                           stop = { line = 16; col = 19 } };
                                         expr = (Var b.c) },
                                       { meta =
                                         { start = { line = 16; col = 22 };
                                           stop = { line = 16; col = 23 } };
                                         expr = (Int 2) }
                                       ))
                                    }
                                  ])
                             }
                           ))
                        };
                      { pmeta =
                        { start = { line = 18; col = 2 };
                          stop = { line = 18; col = 32 } };
                        p =
                        (Forall (
                           { meta =
                             { start = { line = 18; col = 9 };
                               stop = { line = 18; col = 10 } };
                             expr = (Var a) },
                           { meta =
                             { start = { line = 18; col = 14 };
                               stop = { line = 18; col = 15 } };
                             expr = (Var b) },
                           { pmeta =
                             { start = { line = 18; col = 16 };
                               stop = { line = 18; col = 32 } };
                             p =
                             (Seq
                                [{ pmeta =
                                   { start = { line = 18; col = 16 };
                                     stop = { line = 18; col = 23 } };
                                   p =
                                   (Assign (
                                      { meta =
                                        { start = { line = 18; col = 16 };
                                          stop = { line = 18; col = 19 } };
                                        expr = (Var a.b) },
                                      { meta =
                                        { start = { line = 18; col = 22 };
                                          stop = { line = 18; col = 23 } };
                                        expr = (Int 1) }
                                      ))
                                   };
                                  { pmeta =
                                    { start = { line = 18; col = 25 };
                                      stop = { line = 18; col = 32 } };
                                    p =
                                    (Assign (
                                       { meta =
                                         { start = { line = 18; col = 25 };
                                           stop = { line = 18; col = 28 } };
                                         expr = (Var c.a) },
                                       { meta =
                                         { start = { line = 18; col = 31 };
                                           stop = { line = 18; col = 32 } };
                                         expr = (Int 2) }
                                       ))
                                    }
                                  ])
                             }
                           ))
                        }
                      ])
                 },
               { pmeta =
                 { start = { line = 18; col = 36 };
                   stop = { line = 18; col = 43 } };
                 p =
                 (Assign (
                    { meta =
                      { start = { line = 18; col = 36 };
                        stop = { line = 18; col = 39 } };
                      expr = (Var a.a) },
                    { meta =
                      { start = { line = 18; col = 42 };
                        stop = { line = 18; col = 43 } };
                      expr = (Int 1) }
                    ))
                 }
               ))
            };
           { pmeta =
             { start = { line = 20; col = 2 }; stop = { line = 20; col = 31 } };
             p =
             (Seq
                [{ pmeta =
                   { start = { line = 20; col = 3 };
                     stop = { line = 20; col = 21 } };
                   p =
                   (Par
                      [{ pmeta =
                         { start = { line = 20; col = 3 };
                           stop = { line = 20; col = 10 } };
                         p =
                         (Assign (
                            { meta =
                              { start = { line = 20; col = 3 };
                                stop = { line = 20; col = 6 } };
                              expr = (Var a.a) },
                            { meta =
                              { start = { line = 20; col = 9 };
                                stop = { line = 20; col = 10 } };
                              expr = (Int 1) }
                            ))
                         };
                        { pmeta =
                          { start = { line = 20; col = 14 };
                            stop = { line = 20; col = 21 } };
                          p =
                          (Assign (
                             { meta =
                               { start = { line = 20; col = 14 };
                                 stop = { line = 20; col = 17 } };
                               expr = (Var a.b) },
                             { meta =
                               { start = { line = 20; col = 20 };
                                 stop = { line = 20; col = 21 } };
                               expr = (Int 2) }
                             ))
                          }
                        ])
                   };
                  { pmeta =
                    { start = { line = 20; col = 24 };
                      stop = { line = 20; col = 31 } };
                    p =
                    (Assign (
                       { meta =
                         { start = { line = 20; col = 24 };
                           stop = { line = 20; col = 27 } };
                         expr = (Var a.c) },
                       { meta =
                         { start = { line = 20; col = 30 };
                           stop = { line = 20; col = 31 } };
                         expr = (Int 3) }
                       ))
                    }
                  ])
             };
           { pmeta =
             { start = { line = 22; col = 2 }; stop = { line = 22; col = 31 } };
             p =
             (Seq
                [{ pmeta =
                   { start = { line = 22; col = 3 };
                     stop = { line = 22; col = 21 } };
                   p =
                   (Disj (
                      { pmeta =
                        { start = { line = 22; col = 3 };
                          stop = { line = 22; col = 10 } };
                        p =
                        (Assign (
                           { meta =
                             { start = { line = 22; col = 3 };
                               stop = { line = 22; col = 6 } };
                             expr = (Var a.a) },
                           { meta =
                             { start = { line = 22; col = 9 };
                               stop = { line = 22; col = 10 } };
                             expr = (Int 1) }
                           ))
                        },
                      { pmeta =
                        { start = { line = 22; col = 14 };
                          stop = { line = 22; col = 21 } };
                        p =
                        (Assign (
                           { meta =
                             { start = { line = 22; col = 14 };
                               stop = { line = 22; col = 17 } };
                             expr = (Var a.b) },
                           { meta =
                             { start = { line = 22; col = 20 };
                               stop = { line = 22; col = 21 } };
                             expr = (Int 2) }
                           ))
                        }
                      ))
                   };
                  { pmeta =
                    { start = { line = 22; col = 24 };
                      stop = { line = 22; col = 31 } };
                    p =
                    (Assign (
                       { meta =
                         { start = { line = 22; col = 24 };
                           stop = { line = 22; col = 27 } };
                         expr = (Var a.c) },
                       { meta =
                         { start = { line = 22; col = 30 };
                           stop = { line = 22; col = 31 } };
                         expr = (Int 3) }
                       ))
                    }
                  ])
             };
           { pmeta =
             { start = { line = 24; col = 2 }; stop = { line = 24; col = 43 } };
             p =
             (Seq
                [{ pmeta =
                   { start = { line = 24; col = 3 };
                     stop = { line = 24; col = 33 } };
                   p =
                   (Forall (
                      { meta =
                        { start = { line = 24; col = 10 };
                          stop = { line = 24; col = 11 } };
                        expr = (Var a) },
                      { meta =
                        { start = { line = 24; col = 15 };
                          stop = { line = 24; col = 16 } };
                        expr = (Var b) },
                      { pmeta =
                        { start = { line = 24; col = 17 };
                          stop = { line = 24; col = 33 } };
                        p =
                        (Seq
                           [{ pmeta =
                              { start = { line = 24; col = 17 };
                                stop = { line = 24; col = 24 } };
                              p =
                              (Assign (
                                 { meta =
                                   { start = { line = 24; col = 17 };
                                     stop = { line = 24; col = 20 } };
                                   expr = (Var a.b) },
                                 { meta =
                                   { start = { line = 24; col = 23 };
                                     stop = { line = 24; col = 24 } };
                                   expr = (Int 1) }
                                 ))
                              };
                             { pmeta =
                               { start = { line = 24; col = 26 };
                                 stop = { line = 24; col = 33 } };
                               p =
                               (Assign (
                                  { meta =
                                    { start = { line = 24; col = 26 };
                                      stop = { line = 24; col = 29 } };
                                    expr = (Var c.a) },
                                  { meta =
                                    { start = { line = 24; col = 32 };
                                      stop = { line = 24; col = 33 } };
                                    expr = (Int 2) }
                                  ))
                               }
                             ])
                        }
                      ))
                   };
                  { pmeta =
                    { start = { line = 24; col = 36 };
                      stop = { line = 24; col = 43 } };
                    p =
                    (Assign (
                       { meta =
                         { start = { line = 24; col = 36 };
                           stop = { line = 24; col = 39 } };
                         expr = (Var a.a) },
                       { meta =
                         { start = { line = 24; col = 42 };
                           stop = { line = 24; col = 43 } };
                         expr = (Int 1) }
                       ))
                    }
                  ])
             };
           { pmeta =
             { start = { line = 26; col = 2 }; stop = { line = 26; col = 23 } };
             p =
             (Assign (
                { meta =
                  { start = { line = 26; col = 2 };
                    stop = { line = 26; col = 5 } };
                  expr = (Var a.a) },
                { meta =
                  { start = { line = 26; col = 8 };
                    stop = { line = 26; col = 23 } };
                  expr =
                  (App ("&",
                     [{ meta =
                        { start = { line = 26; col = 8 };
                          stop = { line = 26; col = 13 } };
                        expr =
                        (App ("&",
                           [{ meta =
                              { start = { line = 26; col = 8 };
                                stop = { line = 26; col = 9 } };
                              expr = (Var d) };
                             { meta =
                               { start = { line = 26; col = 12 };
                                 stop = { line = 26; col = 13 } };
                               expr = (Var a) }
                             ]
                           ))
                        };
                       { meta =
                         { start = { line = 26; col = 17 };
                           stop = { line = 26; col = 22 } };
                         expr =
                         (App ("|",
                            [{ meta =
                               { start = { line = 26; col = 17 };
                                 stop = { line = 26; col = 18 } };
                               expr = (Var b) };
                              { meta =
                                { start = { line = 26; col = 21 };
                                  stop = { line = 26; col = 22 } };
                                expr = (Var c) }
                              ]
                            ))
                         }
                       ]
                     ))
                  }
                ))
             }
           ])
      }
    }

  $ protocol print parse.spec > parse1.spec && protocol print parse1.spec | protocol print > parse2.spec && diff -uw parse1.spec parse2.spec
