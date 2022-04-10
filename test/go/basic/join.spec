
party r in R (r.a = 1; r.b = 1)

(forall r in R
  (r.a = r.a + 1 || r.b = r.b + 1));

forall r in R
  r.a + r.b == 4 =>
    r.c = 1
