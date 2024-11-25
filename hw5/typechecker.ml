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
  | CArr (ty, exp_h::exp_tl) -> failwith "todo"
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
  | Index (exp_node, exp_node2) -> failwith "todo"
  | Length exp_node -> failwith "todo"
  | CStruct (id, h::tl) -> failwith "todo"
  | Proj (exp_node, id) -> failwith "todo"
  | Call (exp_node, h::tl) -> failwith "todo"
  | Bop (binop, exp_node, exp_node2) -> failwith "todo"
  | Uop (unop, exp_node) -> failwith "todo"
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
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  failwith "todo: implement typecheck_stmt"


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
let typecheck_block (tc : Tctxt.t) (b : Ast.block) (to_ret:ret_ty) : bool =
  failwith "todo: typecheck_block"

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let {frtyp; fname; args; body} = f in
  if check_dups_function args then type_error l ("duplicate arguments")
  else
    let locals = List.map (fun (ty, id) -> (id, ty)) args in
    let tc_ = {tc with locals = locals @ tc.locals} in
    let _ = typecheck_block tc_ body frtyp in
    ()


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
