open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

  let binop_mapping : Ast.binop -> Ll.bop = function
  | Ast.Add -> Ll.Add
  | Ast.Sub -> Ll.Sub
  | Ast.Mul -> Ll.Mul
  | Ast.Eq -> failwith "todo"
  | Ast.Neq -> failwith "todo"
  | Ast.Lt -> failwith "todo"
  | Ast.Lte -> failwith "todo"
  | Ast.Gt  -> failwith "todo"
  | Ast.Gte -> failwith "todo"
  | Ast.And -> Ll.And
  | Ast.Or  -> Ll.Or
  | Ast.IAnd  -> failwith "todo"
  | Ast.IOr -> failwith "todo"
  | Ast.Shl -> Ll.Shl
  | Ast.Shr -> Ll.Lshr
  | Ast.Sar -> Ll.Ashr

let cnd_mapping : Ast.binop -> Ll.cnd = function
  | Ast.Eq -> Ll.Eq
  | Ast.Neq -> Ll.Ne
  | Ast.Lt -> Ll.Slt
  | Ast.Lte -> Ll.Sle
  | Ast.Gt  -> Ll.Sgt
  | Ast.Gte -> Ll.Sge
  | Ast.IAnd  -> failwith "todo"
  | Ast.IOr -> failwith "todo"

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull null -> 
    let ty = cmp_ty (TRef null) in
    ty, Null, []
  | CBool b -> (I1, Const (if b then 1L else 0L), [])
  | CInt i -> (I64, Const i, [])
  | Id id -> 
    let uid = gensym "id" in
    let ty, op = Ctxt.lookup id c in
    let strm = [I (uid, Load (Ptr ty, op))] in
    (ty, Id uid, strm)
  | Index (array, index) ->
    let array_ty, array_op, array_str = cmp_exp c array in
    let index_ty, index_op, index_str = cmp_exp c index in
    let elem_ty = match array_ty with
      | Ptr t -> t
      | _ -> failwith "array type must be pointer"
    in
    let ptr_uid = gensym "elem_ptr" in
    let elem_uid = gensym "elem_val" in
    let gep_instr = Gep (elem_ty, array_op, [index_op]) in

    let load_instr = Load (elem_ty, Id ptr_uid) in
    let strm = array_str @ index_str @ [I (ptr_uid, gep_instr); I (elem_uid, load_instr)] in
    (elem_ty, Id elem_uid, strm)
  | NewArr (array, size) ->
    let size_ty, size_op, size_str = cmp_exp c size in
    let ty, op, strm = oat_alloc_array array size_op in
    ty, op, size_str @ strm
  | Bop (binop, exp1, exp2) ->
    begin match binop with
    | Add | Sub| Mul| IAnd| IOr| Shl| Shr| Sar ->
      let type1, op1, str1 = cmp_exp c exp1 in
      let type2, op2, str2 = cmp_exp c exp2 in
      let ty1, ty2, ty3 = typ_of_binop binop in
      (* if type1 = ty1 && type2 = ty2 then *)
        let binop_ll = binop_mapping binop in
        let uid = gensym "bop" in
        let instr = Binop (binop_ll, cmp_ty ty3, op1, op2) in
        (cmp_ty ty3, Id uid, [I (uid, instr)] @ str2 @ str1) (* not sure about what comes first str1 or 2 *)
      (* else failwith "cmp_exp: type mismatch" *)
    | Eq| Neq| Lt| Lte| Gt| Gte| And| Or ->
      let type1, op1, str1 = cmp_exp c exp1 in
      let type2, op2, str2 = cmp_exp c exp2 in
      let ty1, ty2, ty3 = typ_of_binop binop in
      let cnd_ll = cnd_mapping binop in
      let uid = gensym "cnd" in
      let instr = Icmp (cnd_ll, cmp_ty ty3, op1, op2) in
      (cmp_ty ty3, Id uid, [I (uid, instr)] @ str2 @ str1)
    | _ -> failwith "illegal binop"
    end
  | Uop (unop, exp) ->
    begin match unop with
    | Neg ->
      let type1, op1, str1 = cmp_exp c exp in
      let ty1, ty2 = typ_of_unop unop in
      let uid = gensym "uop" in
      let instr = Binop (Sub, I64, Const 0L, op1) in
      (I64, Id uid, [I (uid, instr)] @ str1)
    | Lognot ->
      let type1, op1, str1 = cmp_exp c exp in
      let ty1, ty2 = typ_of_unop unop in
      let uid = gensym "uop" in
      let instr = Icmp (Eq, I1, op1, Const 0L) in
      (I1, Id uid, [I (uid, instr)] @ str1)
    | Bitnot ->
      let type1, op1, str1 = cmp_exp c exp in
      let ty1, ty2 = typ_of_unop unop in
      let uid = gensym "uop" in
      let instr = Binop (Xor, I64, op1, Const (-1L)) in
      (I64, Id uid, [I (uid, instr)] @ str1)
    | _ -> failwith "illegal unop"
    end
  | _ -> failwith "TODO: cmp_exp"

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

     type elt = 
      | E of uid * Ll.insn      (* hoisted entry block instructions *)

      type stream = elt list
 *)

(* Ctxt.t =   type t = (Ast.id [string] * (Ll.ty * Ll.operand)) list *)
let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Assn (exp1, exp2) -> 
    begin match exp1.elt with
    | Id id -> let var_ty, var_ptr = Ctxt.lookup id c in 
      let (exp2_ty, exp2_ptr, exp2_instr) = cmp_exp c exp2 in
      let store_inst = I (gensym "store", Store(exp2_ty, exp2_ptr, var_ptr)) in
      (c,  exp2_instr @ [store_inst] )

    | Index (arr_exp, i_exp) ->  failwith "array index assignment not implemented penis"
    end 
  | Ret ret -> 
    begin match ret with
      | None -> 
        let term = T (Ret(Void, None)) in
        (c, [term])
      | Some element -> 
        let element_ty, element_op, element_str = cmp_exp c element in
        let strm = [T (Ret(rt, Some element_op))] @ element_str in
        (c, strm)
      | _ -> failwith "ret must be some or none"
    end
  | Decl d -> (* missing store instruction???? *)
    let (name, init) = d in
    let (var_ty, var_op, var_elt) = cmp_exp c init in  
 
    let new_name = gensym name in
    let entry_alloca = E (new_name, Alloca var_ty) in
    (* | Store of ty * operand * operand *)
    let store_alloca = [I (new_name, Store (var_ty, var_op, Id new_name))] in 
    let new_ctxt = Ctxt.add c name (var_ty, Id new_name) in
    (new_ctxt, entry_alloca :: store_alloca @var_elt)
    (* (new_ctxt, var_elt @ [entry_alloca] @ store_alloca) *)
  | If (cond, true_stmt, false_stmt) ->
    let cond_ty, cond_op, cond_elt = cmp_exp c cond in 
    let true_block, true_instrs = cmp_block c rt true_stmt in
    let false_block, false_instrs = cmp_block c rt false_stmt in
    let true_lbl = gensym "true" in
    let false_lbl = gensym "false" in
    let end_lbl = gensym "end" in
    let branch_instr = [T (Cbr (cond_op, true_lbl , false_lbl))] in
    let new_stream = cond_elt @ branch_instr @ [L true_lbl ] @ true_instrs @ [T (Br end_lbl)]@ [L false_lbl] @ false_instrs @ [T (Br end_lbl)] @ [L end_lbl] in
    (c, new_stream)
    (* Todo: check if context needs to be updated with returned cotext from cmp_block *)
  | While (cond, while_stmts) ->
    let cond_ty, cond_op, cond_elt = cmp_exp c cond in 
    let while_lbl = gensym "while" in
    let end_lbl = gensym "end" in
    let cond_lbl = gensym "cond" in
    let while_block, while_instrs = cmp_block c rt while_stmts in
    let branch_instr = [T (Cbr (cond_op, while_lbl, end_lbl))] in
    let new_stream = (* [T (Br cond_lbl)] @ *) [L cond_lbl] @ cond_elt @  branch_instr @ [L while_lbl] @ while_instrs @ [T (Br cond_lbl)] @ [L end_lbl] in
    (c, new_stream)
  | For (vdecls, option_exp, option_stmt, for_stmt) -> (* not sure if it works *)
    let vdecls_streams = List.map (fun vdecl -> 
      let new_c, stmts = cmp_stmt c rt (no_loc (Decl vdecl)) in
      stmts) vdecls in
    let vdecls_stream = List.concat vdecls_streams in
    let update_exp = match option_exp with 
      | Some e -> e
      | None -> no_loc (CBool true)
    in
    let update_stmt = match option_stmt with
      | Some stmt -> [stmt]
      | None -> []
    in
    (* let c, for_instr = cmp_block c rt vdecls_streams in  WTF IS HAPPENING*)
    let update_stmts = for_stmt @ update_stmt in
    let new_new_c, new_stream = cmp_stmt c rt (no_loc (While (update_exp, update_stmts))) in
    (new_new_c, vdecls_stream @ new_stream)
  
  | SCall (exp1, exp2) -> 
    let fname = match exp1.elt with
      | Id id -> id
      | _ -> failwith "invalid function name"
    in
    let f_ptr, f_op = Ctxt.lookup_function fname c in

    match f_ptr with
    | Ptr (Fun (args, ret_ty)) ->

      let arg_results = List.map (cmp_exp c) exp2 in
      let arg_ty_list, arg_op_list, arg_str_list =
        List.fold_right (fun (ty, op, str) (tys, ops, strs) ->
          (ty :: tys, op :: ops, str @ strs)
        ) arg_results ([], [], [])
      in
      let args_list = List.combine arg_ty_list arg_op_list in

      let call_uid = gensym "call" in

      (c, [I (call_uid, Call (ret_ty, f_op, args_list))] @ arg_str_list)


    
  | _ -> failwith "cmp_stmt not implemented"

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
    | Ast.Gvdecl { elt={ name; init } } ->
      let gt = match init.elt with
        | CNull null -> TRef null
        | CInt _ -> TInt
        | CBool _ -> TBool
        | CStr _ -> TRef RString
        | CArr (t, _) -> failwith " arr not implemented"
        | _ -> failwith "cmp_global_ctxt: invalid global initializer"
      in
      Ctxt.add c name (cmp_ty gt, Gid name)
    | _ -> c
  ) c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

 let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let { frtyp; fname; args; body } = f.elt in
  let ret_ty = cmp_ret_ty frtyp in
  let arg_types = List.map (fun (t, _) -> cmp_ty t) args in

  let entry_allocas, arg_bindings = 
    List.fold_left (fun (allocas, bindings) (ty, arg_name) ->
      let ll_ty = cmp_ty ty in
      let uid_alloca = gensym arg_name in
      let alloca_instruction = uid_alloca, Alloca ll_ty in
      let uid_store = gensym "store" in
      let store_instruction = uid_store, Store (ll_ty, Id arg_name, Id uid_alloca) in
      let allocas = E (fst alloca_instruction, snd alloca_instruction) :: E (fst store_instruction, snd store_instruction) :: allocas in
      let bindings = Ctxt.add bindings arg_name (ll_ty, Id uid_alloca) in
      (allocas, bindings)
    ) ([], c) args
  in

  let body_ctxt, body_stream = cmp_block arg_bindings ret_ty body in

  let cfg, gdecls = cfg_of_stream (entry_allocas @ body_stream) in

  let fdecl = {
    f_ty = (arg_types, ret_ty);
    f_param = List.map snd args;
    f_cfg = cfg;
  } in

  fdecl, gdecls


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull null -> (cmp_ty (TRef null), GNull), []
  | CBool b -> (I1, GInt (if b then 1L else 0L)), []
  | CInt i -> (I64, GInt i), []
  | CStr s -> 
    let gid = gensym "str" in
      let len = String.length s + 1 in
      let ty = Array (len, I8) in
      let str_gdecl = (ty, GString s) in
      let ptr_gdecl = (Ptr I8, GBitcast (Ptr ty, GGid gid, Ptr I8)) in
      ptr_gdecl, [(gid, str_gdecl)]
  | _ -> failwith "cmp_gexp not implemented"

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
