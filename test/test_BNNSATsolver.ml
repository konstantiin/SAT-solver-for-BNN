open OUnit2
open SATSolver
open Utils
open BNN

(*
   (x1 + x5 + ~x2) & (x1 + ~x3) & (x2 + x3 + x4)
*)
let cnf1 = [ [ 1; 5; -2 ]; [ 1; -3 ]; [ 2; 3; 4 ] ]

(*
   (x1 + x8 + ~x2) & (x1 + ~x3) & (x2 + x3 + x4) & (~x4 + ~x5) & (x7 + ~x4 + ~x6) & (x5 + x6)
*)
let cnf2 =
  [ [ 1; 8; -2 ]; [ 1; -3 ]; [ 2; 3; 4 ]; [ -4; -5 ]; [ 7; -4; -6 ]; [ 5; 6 ] ]

let cnf3 = [ [ -2 ]; [ -3 ]; [ 2; 3; 4 ]; [ -4; -5 ]; [ -4; -1 ]; [ 5; 1 ] ]

let assignment_printer assignment =
  let str_vars =
    CCPersistentArray.mapi
      (fun i v ->
        let str_val =
          match v.value with
          | TRUE -> "TRUE"
          | FALSE -> "FALSE"
          | UNDEF -> "UNDEF"
        in
        Printf.sprintf "%d: %s" i str_val)
      assignment
  in
  CCPersistentArray.to_list str_vars |> String.concat "\n"

let assignment_cmp a1 a2 =
  Stdlib.( = ) (CCPersistentArray.to_list a1) (CCPersistentArray.to_list a2)

let answer_printer answer =
  match answer with
  | SAT v -> String.concat "" [ string_of_bool_list v; "\n" ]
  | UNSAT _ -> "UNSAT\n"

let assignment_printer_opt assignment_opt =
  match assignment_opt with
  | None -> "None"
  | Some assignment -> assignment_printer assignment

let assignment_cmp_opt a1 a2 =
  match a1 with
  | None -> ( match a2 with None -> true | Some _ -> false)
  | Some as1 -> (
      match a2 with None -> false | Some as2 -> assignment_cmp as1 as2)

let satsolver_unit_tests =
  "SATsolver unit tests"
  >::: [
         ("verify_cnf №1" >:: fun _ -> assert_equal true (verify_cnf cnf1));
         ("verify_cnf №2" >:: fun _ -> assert_equal true (verify_cnf cnf2));
         ( "verify_cnf №3" >:: fun _ ->
           assert_equal false (verify_cnf [ [ 0; 1; 2 ]; [ -1; -2 ] ]) );
         ( "verify_cnf №4" >:: fun _ ->
           assert_equal false (verify_cnf [ [ 0; 1; 3 ]; [ -1; -3 ] ]) );
         ( "opt_unit №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             CCPersistentArray.set undef 1 { value = FALSE; antecender = None }
           in
           assert_equal (Some (-3, [ 1; -3 ])) (opt_unit assignment [ 1; -3 ])
         );
         ( "opt_unit №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 8 { value = FALSE; antecender = None }
           in
           assert_equal
             (Some (-2, [ 1; 8; -2 ]))
             (opt_unit assignment [ 1; 8; -2 ]) );
         ( "opt_unit №3" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             CCPersistentArray.set undef 1 { value = FALSE; antecender = None }
           in
           assert_equal None (opt_unit assignment [ 1; 8; -2 ]) );
         ( "resolve_unit_clause_if_any №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf1 in
             CCPersistentArray.set undef 1 { value = FALSE; antecender = None }
           in
           let expected =
             CCPersistentArray.set assignment 3
               { value = FALSE; antecender = Some [ 1; -3 ] }
           in
           assert_equal ~cmp:assignment_cmp_opt ~printer:assignment_printer_opt
             (Some expected)
             (resolve_unit_clause_if_any cnf1 assignment) );
         ( "resolve_unit_clause_if_any №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 8 { value = FALSE; antecender = None }
           in
           let expected =
             CCPersistentArray.set assignment 2
               { value = FALSE; antecender = Some [ 1; 8; -2 ] }
           in
           assert_equal ~cmp:assignment_cmp_opt ~printer:assignment_printer_opt
             (Some expected)
             (resolve_unit_clause_if_any cnf2 assignment) );
         ( "is_conflict №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf1 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             let false5 =
               CCPersistentArray.set false1 5
                 { value = FALSE; antecender = None }
             in
             let one_resolved_opt = resolve_unit_clause_if_any cnf1 false5 in
             match one_resolved_opt with
             | None -> raise (Failure "resolve_unit_if_any error")
             | Some one_resolved -> (
                 match resolve_unit_clause_if_any cnf1 one_resolved with
                 | None -> raise (Failure "resolve_unit_if_any error")
                 | Some c -> c)
           in
           assert_equal ~printer:string_of_bool false
             (is_conflict assignment [ 2; 3; 4 ]) );
         ( "is_conflict №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false5 =
               CCPersistentArray.set undef 5
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false5 6 { value = FALSE; antecender = None }
           in
           assert_equal ~printer:string_of_bool true
             (is_conflict assignment [ 5; 6 ]) );
         ( "is_conflict №3" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let true5 =
               CCPersistentArray.set undef 5 { value = TRUE; antecender = None }
             in
             let false6 =
               CCPersistentArray.set true5 6
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false6 1 { value = FALSE; antecender = None }
           in
           assert_equal ~printer:string_of_bool true
             (is_conflict assignment [ 1; -5; 6 ]) );
         ( "unit_propagation №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf1 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 5 { value = FALSE; antecender = None }
           in
           let expected =
             ((CCPersistentArray.set assignment 3
                 { value = FALSE; antecender = Some [ 1; -3 ] }
              |> CCPersistentArray.set)
                2
                { value = FALSE; antecender = Some [ 1; 5; -2 ] }
             |> CCPersistentArray.set)
               4
               { value = TRUE; antecender = Some [ 2; 3; 4 ] }
           in
           let got, conflict = unit_propagation cnf1 assignment in
           assert_equal None conflict;
           assert_equal ~cmp:assignment_cmp ~printer:assignment_printer got
             expected );
         ( "unit_propagation №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false5 =
               CCPersistentArray.set undef 5
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false5 6 { value = FALSE; antecender = None }
           in
           let expected = assignment in
           let got, conflict = unit_propagation cnf2 assignment in
           assert_equal (Some [ 5; 6 ]) conflict;
           assert_equal ~cmp:assignment_cmp ~printer:assignment_printer got
             expected );
         ( "conflict_analyzis №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false5 =
               CCPersistentArray.set undef 5
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false5 6 { value = FALSE; antecender = None }
           in
           let a, conflict = unit_propagation cnf2 assignment in
           match conflict with
           | None -> raise (Failure "unit_propagation error")
           | Some c ->
               assert_equal ~printer:string_of_int_list []
                 (conflict_analyzist c a) );
         ( "conflict_analyzis №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false5 =
               CCPersistentArray.set undef 5
                 { value = FALSE; antecender = Some [ -4; -5 ] }
             in
             CCPersistentArray.set false5 6
               { value = FALSE; antecender = Some [ 7; -4; -6 ] }
           in
           let a, conflict = unit_propagation cnf2 assignment in
           match conflict with
           | None -> raise (Failure "unit_propagation error")
           | Some c ->
               assert_equal ~printer:string_of_int_list [ -4; 7 ]
                 (conflict_analyzist c a) );
         ( "not_always_true №1" >:: fun _ ->
           assert_equal true (not_always_true [ 1; -3 ]) );
         ( "not_always_true №2" >:: fun _ ->
           assert_equal false (not_always_true [ 3; -3 ]) );
         ( "not_always_true №3" >:: fun _ ->
           assert_equal true (not_always_true [ 1; 2; 3; 4 ]) );
         ( "not_always_true №4" >:: fun _ ->
           assert_equal false (not_always_true [ 1; 2; 3; 4; -2 ]) );
         ( "preprocess №1" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list
             [ [ -3; 1 ]; [ -2; 1; 5 ]; [ 2; 3; 4 ] ]
             (preprocess cnf1) );
         ( "preprocess №2" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list
             [ [ -2; 1; 5 ]; [ 2; 3; 4 ] ]
             (preprocess [ [ 1; 5; -2 ]; [ 3; -3 ]; [ 2; 3; 4 ] ]) );
         ( "preprocess №3" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list
             [ [ -2; 1; 5 ]; [ 2; 3; 4 ] ]
             (preprocess [ [ 1; 5; -2; 5 ]; [ 3; -3 ]; [ 2; 3; 4 ] ]) );
         ( "preprocess №4" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list
             [ [ -2; 1; 5 ]; [ 2; 3; 4 ] ]
             (preprocess
                [ [ 1; 5; -2; 5 ]; [ 3; -3 ]; [ 2; 3; 4 ]; [ 3; 2; 4 ] ]) );
         ( "get_undef_var №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false5 =
               CCPersistentArray.set undef 5
                 { value = FALSE; antecender = Some [ -4; -5 ] }
             in
             CCPersistentArray.set false5 6
               { value = FALSE; antecender = Some [ 7; -4; -6 ] }
           in
           assert_equal (Some 1) (get_undef_var assignment) );
         ( "get_undef_var №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             CCPersistentArray.set undef 1
               { value = FALSE; antecender = Some [ -4; -5 ] }
           in
           assert_equal (Some 2) (get_undef_var assignment) );
         ( "get_undef_var №3" >:: fun _ ->
           let assignment =
             let undef = init_assignment [ [ 1; 2 ] ] in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 2 { value = TRUE; antecender = None }
           in
           assert_equal None (get_undef_var assignment) );
         ( "assignment_to_bool_list №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment [ [ 1; 2 ] ] in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 2 { value = TRUE; antecender = None }
           in
           assert_equal [ false; true ] (assignment_to_bool_list assignment) );
         ( "assignment_to_bool_list №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment [ [ 1; 2 ] ] in
             CCPersistentArray.set undef 1 { value = FALSE; antecender = None }
           in
           assert_raises (Failure "could not convert to bool lists") (fun () ->
               assignment_to_bool_list assignment) );
         ( "exists_unsat №1" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf1 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 5 { value = FALSE; antecender = None }
           in
           assert_equal ~printer:string_of_bool false
             (exists_unsat cnf1 assignment) );
         ( "exists_unsat №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf1 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false1 5 { value = FALSE; antecender = None }
           in
           assert_equal ~printer:string_of_bool true
             (exists_unsat [ [ 2; 3 ]; [ 1; 5 ] ] assignment) );
         ( "exists_unsat №3" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf1 in
             let false1 =
               CCPersistentArray.set undef 1
                 { value = FALSE; antecender = None }
             in
             let false5 =
               CCPersistentArray.set false1 5
                 { value = FALSE; antecender = None }
             in
             CCPersistentArray.set false5 2 { value = TRUE; antecender = None }
           in
           assert_equal ~printer:string_of_bool true
             (exists_unsat [ [ 2; 3; 4 ]; [ -2; 1; 5 ] ] assignment) );
         ( "cdcl №1" >:: fun _ ->
           assert_equal ~printer:answer_printer
             (SAT [ true; true; true; true; true ])
             (cdcl cnf1) );
         ( "cdcl №2" >:: fun _ ->
           assert_equal ~printer:answer_printer
             (SAT [ true; true; true; true; false; true; true; true ])
             (cdcl cnf2) );
         ( "cdcl №3" >:: fun _ ->
           assert_equal
             ~cmp:(fun r1 r2 ->
               match r1 with
               | UNSAT _ -> ( match r2 with UNSAT _ -> true | SAT _ -> false)
               | SAT res1 -> (
                   match r2 with
                   | UNSAT _ -> false
                   | SAT res2 -> Stdlib.( = ) res1 res2))
             ~printer:answer_printer (UNSAT []) (cdcl cnf3) );
       ]

let _ = run_test_tt_main satsolver_unit_tests

let bnn_unit_tests =
  "BNN unit tests"
  >::: [
         ( "at_least_k №1" >:: fun _ ->
           let (cnf, _), v =
             at_least_k [ 1; 2; 3 ] 2 []
               { weights = [ 3; 2; 1 ]; extra_vars = [] }
           in
           assert_equal ~printer:string_of_int 16 v;
           assert_equal ~printer:string_of_int_list_list
             [
               [ -9; -3; 15 ];
               [ 8; 13; -14 ];
               [ -9; -12; 16 ];
               [ 8; 3; -15 ];
               [ -10; -3; 16 ];
               [ 9; 13; -15 ];
               [ -10; -12; 17 ];
               [ 9; 3; -16 ];
               [ -11; -3; 17 ];
               [ 10; 13; -16 ];
               [ -11; -12; 18 ];
               [ 10; 3; -17 ];
               [ 12 ];
               [ 18 ];
               [ -13 ];
               [ -14 ];
               [ -1; -2; 9 ];
               [ 5; 7; -8 ];
               [ -1; -6; 10 ];
               [ 5; 2; -9 ];
               [ -4; -2; 10 ];
               [ 1; 7; -9 ];
               [ -4; -6; 11 ];
               [ 1; 2; -10 ];
               [ 6 ];
               [ 11 ];
               [ -7 ];
               [ -8 ];
               [ 4 ];
               [ -5 ];
             ]
             cnf );
         ( "unflatten №1" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list
             [ [ 1; 2; 3; 4 ]; [ 5; 4; 3; 2 ] ]
             (unflatten 2 4 [ 1; 2; 3; 4; 5; 4; 3; 2 ]) );
       ]

let _ = run_test_tt_main bnn_unit_tests
