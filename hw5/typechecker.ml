open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  let { locals; globals; structs } = c in
  (* todo: check what c needs to be used for *)
  match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TRef ref1, TRef ref2 -> subtype_ref c ref1 ref2
  (* | TNullRef ref1, TRef ref2 -> subtype_ref c ref1 ref2 *)
  | TRef ref1, TNullRef ref2 -> subtype_ref c ref1 ref2
  | TNullRef ref1, TNullRef ref2 -> subtype_ref c ref1 ref2
  | _ -> false



(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  let { locals; globals; structs } = c in
  match t1, t2 with
  | RString, RString -> true
  | RStruct s1, RStruct s2 -> s1 = s2
  | RArray t1, RArray t2 -> subtype c t1 t2
  | RFun (args1, ret1), RFun (args2, ret2) ->
    let l1 = List.length args1 in
    let l2 = List.length args2 in
    let rec arg_subtype c args1 args2 = 
      match args1, args2 with
      | [], [] -> true
      | a1::args1, a2::args2 -> subtype c a1 a2 && arg_subtype c args1 args2
      | _ -> false
    in
    begin match ret1, ret2 with
    | RetVoid, RetVoid -> l1 = l2 &&
      arg_subtype c args1 args2
    | RetVal ret1, RetVal ret2 ->
      l1 = l2 &&
      arg_subtype c args1 args2 &&
      subtype c ret1 ret2
    end
  | _ -> false


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TBool | TInt -> ()
  | TRef reft -> typecheck_refty l tc reft
  | TNullRef reft -> typecheck_refty l tc reft
  | _ -> failwith "illegal type"
  (* todo: use type_error *)


and typecheck_refty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray t -> typecheck_ty l tc t
  | RStruct id ->
    let strct = lookup_struct id tc in
    List.iter (fun f -> typecheck_ty l tc f.ftyp) strct
  | RFun (args, retty) ->
    List.iter (typecheck_ty l tc) args;
    match retty with
    | RetVoid -> ()
    | RetVal t -> typecheck_ty l tc t

  | _ -> failwith "illegal reftype"


(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  let exp = e.elt in
  begin match exp with
  | CNull rty -> 
    let tref = TRef rty in
    if typecheck_ty e c tref = () then
      TNullRef rty
    else
      type_error e "illegal CNull"
  | CBool b -> TBool
  | CInt i -> TInt
  | CStr str -> TRef RString
  | Id id -> 
    let id_ty = Tctxt.lookup_local_option id c in
    begin match id_ty with
    | Some ty -> ty
    | None -> 
      let id_ty_global = Tctxt.lookup_global_option id c in
      begin match id_ty with
      | Some ty -> ty
      | None -> type_error e "illegal Id"
      end
    end
  | CArr (ty, exp_node_list) ->List.iter (fun exp_node -> (* checks if subtype but not if valid type  . Is this equivalent? *)
    let exp_ty = typecheck_exp c exp_node in
    if not (subtype c exp_ty ty) then type_error exp_node "not subtype in carr") exp_node_list; TRef (RArray ty)
  | NewArr (ty, exp_node1, id, exp_node2) -> 
    let exp1 = exp_node1.elt in
    let exp2 = exp_node2.elt in
    let type_check = typecheck_ty exp_node1 c ty in
    let id_option = lookup_local_option id c in
    let local_check = 
      match id_option with
      | Some _ -> false
      | None -> true
    in
    failwith "todo newarr"
  | Index (exp_node, exp_node2) ->
    let exp_ty = typecheck_exp c exp_node in
    let exp_ty2 = typecheck_exp c exp_node2 in 
    begin match exp_ty with
      | TRef (RArray arr_ty) ->  if exp_ty2 = TInt then arr_ty else type_error e "index op must be an int type"
      | _ -> type_error e "index op must be an array type"
    end
  | Length exp_node ->
    let exp_ty = typecheck_exp c exp_node in 
    begin match exp_ty with
    | TRef (RArray arr_ty) -> TInt
    | _ -> type_error e "len op must be an array type"
    end
  | CStruct (id, id_node_list) ->failwith "TODO"
(*     match Tctxt.lookup_struct id c with
    | Some t ->List.iter (fun exp_node -> 
      let exp_ty = typecheck_exp c exp_node in
      ) id_node_list; 
      
      TRef (RStruct id)
    | None -> type_error e ("Struct not there") *)

    

  | Proj (exp_node, id) ->
    let struct_ty = typecheck_exp c exp_node in
    begin match struct_ty with
      | TRef (RStruct struc) | TNullRef (RStruct struc) -> 
        let struct_fields = match Tctxt.lookup_struct_option struc c with
        | Some fields -> fields
        | None -> type_error e ("Struc gone")
        in
        let field = List.find_opt (fun field -> field.fieldName = id) struct_fields in
        begin match field with
        | Some f -> f.ftyp  (* Return the field's type *)
        | None -> type_error e ("field not found")
        end
    | _ -> type_error e "Expression is not a struct type"
    end
  | Call (exp_node, args_list) -> (* todo geth void function here? *)
    let funct_ty = typecheck_exp c exp_node in
    begin match funct_ty with
    | TRef (RFun (para_ty, ret_ty)) ->
      let args_ty = List.map (typecheck_exp c) args_list in
      if List.length para_ty <> List.length args_ty then type_error e "arg count does not match para count";
        List.iter2 (fun arg_ty1 arg_ty2 ->
          if not (subtype c arg_ty1 arg_ty2) then
            type_error e ("not subtype in call")  
        ) args_ty para_ty; 
        begin match ret_ty with
          | RetVal ty -> ty
          | RetVoid -> type_error e "no void allowedß?"
        end
    | _ -> type_error e ("exp is not fun")
    end

    
  | Bop (binop, exp_node, exp_node2) ->
    let exp1_ty = typecheck_exp c exp_node in
    let exp2_ty = typecheck_exp c exp_node2 in
    begin match binop with
      | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (* type int ops *)
        if (exp1_ty = TInt && exp2_ty = TInt) then exp1_ty else type_error e "One or both are not int type in binry operation"
      | Lt | Lte | Gt | Gte -> (* type cmp ops *)
        if (exp1_ty = TInt && exp2_ty = TInt) then TBool else type_error e "One or both are not int type in binry operation"
      | And | Or -> (* type bool ops *)
        if(exp1_ty = TBool && exp2_ty = TBool) then TBool else type_error e "One or both are not int type in binry operation"
      | Eq -> (* type eq either exp1 is subtype of ex2 or the other way around *)
        if subtype c exp1_ty exp2_ty  && subtype c exp2_ty exp1_ty then TBool else type_error e "penis"
      | Neq -> 
        if subtype c exp1_ty exp2_ty  && subtype c exp2_ty exp1_ty then TBool else type_error e "penis"
      | _ ->failwith "pattern matching bop"
    end
  | Uop (unop, exp_node) ->
    let exp_ty = typecheck_exp c exp_node in
    begin match unop with
      | Neg | Bitnot -> if(exp_ty = TInt) then TInt else type_error e "One or both are not int type in unary operation"
      | Lognot -> if(exp_ty = TBool) then TBool else type_error e "One or both are not int type in unary operation"
    end
  end
  

let typecheck_function_ty (tc: Tctxt.t) (fdecl_node: Ast.fdecl Ast.node) : Ast.ty =
  let {elt=fdecl} = fdecl_node in
  let {frtyp; fname; args; body} = fdecl in
  let arg_types = List.map (fun (ty, _) -> ty) args in
  let fun_exp = TRef (RFun (arg_types, frtyp)) in
  if typecheck_ty fdecl_node tc fun_exp = () then
    fun_exp
  else
    type_error fdecl_node "illegal function type"

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let check_assign (tc: Tctxt.t) (id: Ast.id) : bool =
  let check_local =
    let id_option = lookup_local_option id tc in
    begin match id_option with
    | Some _ -> true
    | None -> false
    end
  in
  let check_not_global_function_id =
    let id_option = lookup_global_option id tc in
    begin match id_option with
    | Some id -> 
      begin match id with
      | TRef (RFun _) -> false
      | _ -> true
      end
    | None -> true
    end
  in
  check_local || check_not_global_function_id

let typecheck_vdecl (tc : Tctxt.t) (s : Ast.stmt node) (vdecl : Ast.vdecl) : Tctxt.t =
  let (id, exp_node) = vdecl in
  let exp = exp_node.elt in
  let exp_ty = typecheck_exp tc exp_node in
  let id_used = Tctxt.lookup_local_option id tc in
  let id_not_used = 
    match id_used with
    | Some _ -> false
    | None -> true
  in
  if id_not_used then
    Tctxt.add_local tc id exp_ty
  else
    type_error s "illegal declaration"

let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  let context = ref tc in
  let stmt = s.elt in
  begin match stmt with
  | Assn (exp_node1, exp_node2) ->
    let exp1 = exp_node1.elt in
    let exp2 = exp_node2.elt in
    let exp1_ty = typecheck_exp !context exp_node1 in
    let exp2_ty = typecheck_exp !context exp_node2 in
    let check_subtype = subtype !context exp2_ty exp1_ty in
    let check_assumption = 
      match exp1 with
      | Id id -> check_assign !context id
      | _ -> failwith "todo: remaining assn stuff"
    in
    if check_subtype && check_assumption then
      !context, false
    else
      type_error s "illegal assignment"

  | Decl vdecl ->
    let tc_new = typecheck_vdecl !context s vdecl in
    tc_new, false
  | Ret (exp_node_option) -> 
    begin match exp_node_option with
    | Some exp_node -> 
      begin match to_ret with
      | RetVoid -> type_error s "illegal return"
      | RetVal ty ->
        let exp = exp_node.elt in
        let exp_ty = typecheck_exp !context exp_node in
        let check_subtype = subtype !context exp_ty ty in
        if check_subtype then
          !context, true
        else
          type_error s "illegal return"
      end
    | None ->
      begin match to_ret with
      | RetVoid -> !context, true
      | RetVal _ -> type_error s "illegal return"
      end
    end
  | SCall (exp_node, exp_node_list) ->
    let exp = exp_node.elt in
    let exp_ty = typecheck_exp !context exp_node in
    begin match exp_ty with
    | TRef RFun (args, ret_ty) ->
      begin match ret_ty with
      | RetVoid ->
        let typecheck_args = List.map (fun exp_node -> typecheck_exp !context exp_node) exp_node_list in
        let check_subtype = List.map2 (fun arg1 arg2 -> subtype !context arg1 arg2) args typecheck_args in
        if List.for_all (fun x -> x) check_subtype then
          !context, false
        else
          type_error s "illegal call"
      | RetVal _ -> failwith "todo: return value"
      end
    | _ -> type_error s "illegal call"
    end
  | If (exp_node, stmt_node_list1, stmt_node_list2) ->
    let exp = exp_node.elt in
    let exp_ty = typecheck_exp !context exp_node in
    let typecheck_block1 = typecheck_block !context stmt_node_list1 to_ret in
    let typecheck_block2 = typecheck_block !context stmt_node_list2 to_ret in
    if exp_ty = TBool && typecheck_block1 && typecheck_block2 then
      !context, true
    else
      type_error s "illegal if"
  | Cast (rty, id, exp_node, stmt_node_list1, stmt_node_list2) -> failwith "todo: cast"
  | For (vdecl_list, exp_node_option1, stmt_node_option2, stmt_node_list) ->
    failwith "todo: for"
  | While (exp_node, stmt_node_list) ->
    let exp = exp_node.elt in
    let exp_ty = typecheck_exp !context exp_node in
    let typecheck_block = typecheck_block !context stmt_node_list to_ret in
    if exp_ty = TBool && typecheck_block then
      !context, false
    else
      type_error s "illegal while"
  end

and typecheck_block (tc : Tctxt.t) (block : Ast.block) (ret_ty:ret_ty) : bool =
  let rec typecheck_stmts (tc : Tctxt.t) (stmts : Ast.stmt Ast.node list) (ret_ty:ret_ty) : bool =
    match stmts with
    | [] -> false
    | stmt::stmts ->
      let (tc_, ret) = typecheck_stmt tc stmt ret_ty in
      if ret then true (* todo?: check if return is not at the end of the block *)
      else typecheck_stmts tc_ stmts ret_ty
  in
  typecheck_stmts tc block ret_ty


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let rec check_dups_function args =
  match args with
  | [] -> false
  | h::tl -> (List.exists (fun x -> x = h) tl) || check_dups_function tl

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let {frtyp; fname; args; body} = f in
  if check_dups_function args then type_error l ("duplicate arguments")
  else
    let locals = List.map (fun (ty, id) -> (id, ty)) args in
    let tc_ = {tc with locals = locals @ tc.locals} in
    let typecheck_bl = typecheck_block tc_ body frtyp in
    if not typecheck_bl then type_error l "function does not return"
    else ()


(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let context = ref Tctxt.empty in

  List.iter (fun decl ->
    match decl with
    | Gtdecl tdecl_node ->
      let {elt=(id, fs)} = tdecl_node in
      if check_dups fs then
        type_error tdecl_node "repeated fields in struct"
      else        
        List.iter (fun f -> 
          if (typecheck_ty tdecl_node !context f.ftyp) <> () then
            type_error tdecl_node "illegal struct"

        ) fs;
        context := Tctxt.add_struct !context id fs
    | _ -> ()
  ) p;
  !context

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let context = ref tc in
  List.iter(fun decl ->
    match decl with
    | Gfdecl fdecl_node ->
      let {elt=fdecl} = fdecl_node in
      let {frtyp; fname; args; body} = fdecl in
      let fty = typecheck_function_ty tc fdecl_node in
      context := Tctxt.add_global !context fname fty

    | _ -> ()
  ) p;
  !context

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let context = ref tc in
  List.iter(fun decl ->
    match decl with
    | Gvdecl gdecl_node ->
      let {elt=gdecl} = gdecl_node in
      let {name; init} = gdecl in
      let ty = typecheck_exp !context init in
      context := Tctxt.add_global !context name ty
    | _ -> ()
  ) p;
  !context


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
