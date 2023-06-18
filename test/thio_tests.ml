module TypecheckerTest = struct
  let typechecks name ~expr ~typ =
    let typecheck () =
      let expected = typ in
      let actual =
        Thio.typecheck expr
        |> Thio.qual_type_to_string
      in
      Alcotest.(check (string) "" expected) actual
    in
    Alcotest.test_case name `Quick typecheck

  let tests = [
      typechecks "literal integer typechecks"
        ~expr:"1"
        ~typ:"(Num v0) => v0";
  ]
end

let () =
  Alcotest.run "Thio tests" [
    "Typechecker", TypecheckerTest.tests;
  ]

