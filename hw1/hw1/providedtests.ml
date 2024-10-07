open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let ctxt = [("x", 5L); ("y", 7L)]

(* let e1 = Const 42L         *)
let e2 = Add (Const 1L, Const 2L)     
let e6 = Mult (Var "x", Const 3L)     
let e4 = Neg (Var "y")                
let e5 = Add (e6, e4)      

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);
  Test ("Student-Provided Tests For Problem 4-4", [
    ("interpret4", assert_eqf (fun () -> interpret ctxt2 e3) (-63L));
  ]);

  Test ("4-5", [
    ("optimize3", assert_eqf (fun () -> optimize (Mult(Const 0L, Var "x"))) (Const 0L));
    ("optimize4", assert_eqf (fun () -> optimize (Mult(Var "x + 3", Const 0L))) (Const 0L));
    ("optimize5", assert_eqf (fun () -> optimize (Mult(Const 1L, Var "x + 5"))) (Var "x + 5"));
    ("optimize6", assert_eqf (fun () -> optimize (Mult(Var "x", Const 1L))) (Var "x"));
    ("optimize7", assert_eqf (fun () -> optimize (Add(Const 0L, Var "x"))) (Var "x"));
    ("optimize8", assert_eqf (fun () -> optimize (Add(Var "x + 7", Const 0L))) (Var "x + 7"));
    ("optimize9", assert_eqf (fun () -> optimize (Add(Const 0L, Add(Const 3L, Mult(Const 0L, Var "x"))))) (Const 3L));
    ("optimize10", assert_eqf (fun () -> optimize (Mult(Const 0L, Add(Const 3L, Var "x")))) (Const 0L));
    ("optimize11", assert_eqf (fun () -> optimize (Neg(Const 5L))) (Const (-5L)));
    ("optimize12", assert_eqf (fun () -> optimize (Neg(Neg(Var "x")))) (Var "x"));
    ("optimize13", assert_eqf (fun () -> optimize (Add(Const 2L, Add(Const 3L, Const 5L)))) (Const 10L));
    ("optimize14", assert_eqf (fun () -> optimize (Mult(Add(Const 2L, Const 3L), Const 4L))) (Const 20L));
    ("optimize15", assert_eqf (fun () -> optimize (Add(Mult(Const 0L, Var "y"), Add(Const 5L, Const 0L)))) (Const 5L));
    ("optimize16", assert_eqf (fun () -> optimize (Add(Mult(Var "x", Const 0L), Add(Var "y", Mult(Const 0L, Var "z"))))) (Var "y"));
    ("optimize17", assert_eqf (fun () -> optimize (Add(Var "x", Var "y"))) (Add(Var "x", Var "y")));
  ]);

           

(* Test cases *)
  Test ("Student-Provided Tests For Problem 5", [
  (* ("test_const", assert_eqf (fun () -> run ctxt (compile e1)) 42L); *)
  ("test_add_consts", assert_eqf (fun () -> run ctxt (compile e2)) 3L);
  ("test_mult_var_const", assert_eqf (fun () -> run ctxt (compile e6)) 15L);  (* 5 * 3 *)
  ("test_neg_var", assert_eqf (fun () -> run ctxt (compile e4)) (-7L));
  ("test_add_complex", assert_eqf (fun () -> run ctxt (compile e5)) 8L);     (* 15 + (-7) *)
])
  
] 
