let%expect_test "actions" =
  Lib.print ~project_party:(Some "C") ~ast:false ~types:false ~actions:true
    ~latex:false ~grain:(Some "standard")
    (`String {|
  party c in C ()
  forall c in C
    c.a = 1
  |});
  [%expect
    {|
    digraph G {
      1 [label="CChangeA1\n{start(Cmain)}\na = 1\n{Cmain = 1}\n"];
    }
|}]