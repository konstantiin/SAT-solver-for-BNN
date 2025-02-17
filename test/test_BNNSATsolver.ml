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
    Assign.mapi
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
  Assign.to_list str_vars |> String.concat "\n"

let assignment_cmp a1 a2 = Stdlib.( = ) (Assign.to_list a1) (Assign.to_list a2)

let answer_printer answer =
  match answer with
  | SAT v -> String.concat "" [ string_of_bool_list v; "\n" ]
  | UNSAT _ -> "UNSAT\n"

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
             Assign.set undef 1 { value = FALSE; antecender = None }
           in
           assert_equal (Some (-3, [ 1; -3 ])) (opt_unit assignment [ 1; -3 ])
         );
         ( "opt_unit №2" >:: fun _ ->
           let assignment =
             let undef = init_assignment cnf2 in
             let false1 =
               Assign.set undef 1 { value = FALSE; antecender = None }
             in
             Assign.set false1 8 { value = FALSE; antecender = None }
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
           let clause_by_var = get_clause_by_var assignment cnf1 in
           let got, conflict =
             unit_propagation (List.to_seq cnf1) clause_by_var assignment
           in
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
           let clause_by_var = get_clause_by_var assignment cnf2 in
           let got, conflict =
             unit_propagation (List.to_seq cnf2) clause_by_var assignment
           in
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
           let clause_by_var = get_clause_by_var assignment cnf2 in
           let a, conflict =
             unit_propagation (List.to_seq cnf2) clause_by_var assignment
           in
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
           let clause_by_var = get_clause_by_var assignment cnf2 in
           let a, conflict =
             unit_propagation (List.to_seq cnf2) clause_by_var assignment
           in
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
             ~printer:answer_printer
             (UNSAT (0, []))
             (cdcl cnf3) );
       ]

let _ = run_test_tt_main satsolver_unit_tests

module LinearNet = Sequantial (struct
  let s = [ Linear (2, 1); Linear (1, 2) ]
end)

let bnn_unit_tests =
  "BNN unit tests"
  >::: [
         ( "at_least_k №1" >:: fun _ ->
           let (cnf, _), v =
             at_least_k [ 3; 4; 5 ] 2 [ [ 1 ]; [ -2 ] ]
               {
                 weights = [ 5; 4; 3 ];
                 extra_vars = [ 2; 1 ];
                 g_true = 1;
                 g_false = 2;
               }
           in
           assert_equal ~printer:string_of_int 9 v;
           assert_equal ~printer:string_of_int_list_list
             [
               [ -6; -5; 8 ];
               [ 5; -8 ];
               [ -6; 9 ];
               [ 6; -8 ];
               [ -7; -5; 9 ];
               [ 6; 5; -9 ];
               [ -7; 10 ];
               [ 7; -9 ];
               [ -5; 10 ];
               [ 7; 5; -10 ];
               [ -3; -4; 6 ];
               [ 4; -6 ];
               [ -3; 7 ];
               [ 3; -6 ];
               [ -4; 7 ];
               [ 3; 4; -7 ];
               [ 1 ];
               [ -2 ];
             ]
             cnf );
         ( "unflatten №1" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list
             [ [ 1; 2; 3; 4 ]; [ 5; 4; 3; 2 ] ]
             (unflatten 2 4 [ 1; 2; 3; 4; 5; 4; 3; 2 ]) );
         ( "enumerate №1" >:: fun _ ->
           assert_equal
             [ (1, 0); (2, 1); (3, 2); (9, 3) ]
             (enumerate [ 1; 2; 3; 9 ] 4) );
         (* ( "get_cnf №1" >:: fun _ ->
           assert_equal ~printer:string_of_int_list_list [

           ]
             (LinearNet.get_cnf [ ([ 1; 1 ], 1) ]) ); *)
       ]

let _ = run_test_tt_main bnn_unit_tests
