module TypecheckerTest = struct
  let tests = [
      Alcotest.test_case "Test works" `Quick
         (fun () -> Alcotest.(check (int) "" 123) 123)
  ]
end

let () =
  Alcotest.run "Thio tests" [
    "Typechecker", TypecheckerTest.tests;
  ]
