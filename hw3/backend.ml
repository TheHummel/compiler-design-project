(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be represented
   in 64 bit. This greatly simplifies code generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list (* maping Named types (as string ) then its type *)
            ; layout : layout (* Local identifiers to there x86 operation *)
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)

(* type ins = opcode * operand list *)
(* Fertig *)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  let {tdecls; layout} = ctxt in 
  fun operand ->
    match operand with 
    | Null -> (Movq, [Imm (Lit 0L); dest])
    | Const c -> (Movq, [Imm (Lit c); dest])
    (* globale identifier *)
    | Gid g -> 
      let mangled_name = Platform.mangle g in
      (Leaq, [Ind3 (Lbl mangled_name, Rip); dest])
    (* finds value and stores it in dest   *)
    | Id i -> (Movq, [lookup layout i; dest])  



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

let arg_loc (n : int) : operand =
  if n<6 then 
    match n with 
    | 0 -> Reg Rdi
    | 1 -> Reg Rsi
    | 2 -> Reg Rdx
    | 3 -> Reg Rcx
    | 4 -> Reg R08
    | 5 -> Reg R09
    | _ -> failwith "n should not be neg"
  else 
    Ind3 (Lit (Int64.of_int (((n-6)+2)*(8))), Rbp) 


    
let compile_call (ctxt:ctxt) (fn:gid) (args:(Ll.ty * Ll.operand) list) : X86.ins list =
  let {tdecls; layout} = ctxt in
  let n_args = List.length args in


  let moves = List.mapi (
    fun i (_, operand) -> (
      let dest = arg_loc i in
      if i < 6 then
        [compile_operand ctxt dest operand]
      else
        [compile_operand ctxt (Reg R10) operand; (Pushq, [Reg R10])]
    )
  ) args in


  let arg_moves = List.flatten moves in


  let call = [(Callq, [Imm (Lbl (Platform.mangle fn))])] in
  let cleanup = [(Addq, [Imm (Lit (Int64.of_int (8 * if n_args>6 then List.length arg_moves - 6 else 0))); Reg Rsp]) ] in
  arg_moves @ call @ cleanup


    

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  match t with
  | Void | I8 | Fun _ -> 0
  | I1 | I64 | Ptr _ -> 8
  | Struct ts -> List.fold_left (fun acc t -> acc + size_ty tdecls t) 0 ts
  | Array (n, t) -> n * size_ty tdecls t
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)
  
  (* Fertig *)




(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  let {tdecls; layout} = ctxt in
  let (ty, operand) = op in
  begin match ty with
  | Ptr t -> 
    let t_size = Int64.of_int (size_ty tdecls t) in
    let coperand_op = [compile_operand ctxt (Reg R11) operand] in
    let h_path::tl_path = path in
    let coperand_h = [compile_operand ctxt (Reg R10) h_path] in
    let temp_reg = (Imulq, [Imm (Lit t_size); Reg R10]) in
    let add = (Addq, [Reg R10; Reg R11]) in
    let rec compile_path type_path path = 
      begin match (type_path, path) with
      | (Namedt tid, path_rest) ->
        let type_namedt = lookup tdecls tid in
        compile_path type_namedt path_rest
      | (Array (_, type_array), h::tl) ->
        let entry_size = Int64.of_int (size_ty tdecls type_array) in
        let cpath = [compile_operand ctxt (Reg R10) h] in
        let temp_reg_r = (Imulq, [Imm (Lit entry_size); Reg R10]) in
        let add_r = (Addq, [Reg R10; Reg R11]) in
        cpath @ [temp_reg_r; add_r] @ compile_path type_array tl
      | (Struct strc, Const c::tl) -> 
        let rec sum i list = 
          match (i, list) with
          | (0L, h::_) -> (0L, h)
          | (i, h::tl) -> 
            let (acc, tp) = sum (Int64.sub i 1L) tl in 
            (Int64.add acc (Int64.of_int (size_ty tdecls h)), tp)
          | _ -> failwith "failed sum"
        in
        let (offset, tp) = sum c strc in
        (Addq, [Imm (Lit offset); Reg R11])::(compile_path tp tl)
      | (_, []) -> []
      | _ -> failwith "should be namedt, array or struct"

      end
    in
    coperand_op @ coperand_h @ [temp_reg; add] @ compile_path t tl_path

  | _ -> failwith "should be pointer type"
  end




(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
(* so wie ich es verstanden habe, ctxt zusatand aller variablen, uid variable in die geschrieben wird, insn die instruction dafür *)
(* TODO *)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  match i with
  (* lade die values von unseren beiden operands einfach mal in R10 and 11. Hoffe das passt so *)
  | Binop (operation, ty, operand1, operand2) -> 
    let dest = lookup ctxt.layout uid in
    let {tdecls; layout} = ctxt in
    let coperand1 = [(compile_operand ctxt (Reg R11)) operand1 ] in
    let coperand2 = [(compile_operand ctxt (Reg R10)) operand2]  in
    coperand1 @ coperand2 @ (
    match operation with
    | Add -> [(Addq, [(Reg R10); (Reg R11)])]
    | Sub -> [(Subq, [(Reg R10); (Reg R11)])]
    | Mul -> [(Imulq, [(Reg R10); (Reg R11)])]
    | Shl | Lshr | Ashr -> 
      begin match operand2 with
      | Const c -> 
        begin match operation with
        | Shl -> [(Shlq, [(Imm (Lit c)); (Reg R11)])]
        | Lshr -> [(Shrq, [(Imm (Lit c)); (Reg R11)])]
        | Ashr -> [(Sarq, [(Imm (Lit c)); (Reg R11)])]
      
      end
      | _ -> failwith "Shl operand1 should be constant"
    end
    | And -> [(Andq, [(Reg R10); (Reg R11)])]
    | Or -> [(Orq, [(Reg R10); (Reg R11)])]
    | Xor -> [(Xorq, [(Reg R10); (Reg R11)])]
    ) @ [(Movq, [(Reg R11); dest])]

  |Icmp (cnd, ty, operand1, operand2) ->
    let {tdecls; layout} = ctxt in
    let coperand1 = [(compile_operand ctxt (Reg R11)) operand1 ] in
    let coperand2 = [(compile_operand ctxt (Reg R10)) operand2]  in
    coperand1 @ coperand2 @ [(Movq, [Imm (Lit 0L); Reg R09])] @ [
      (Cmpq, [(Reg R10); (Reg R11)]);
      (Set (compile_cnd cnd), [Reg R09]);
      (Movq, [Reg R09; lookup layout uid])
    ]

  | Alloca ty ->
    let {tdecls; layout} = ctxt in
    let alloc_size = size_ty tdecls ty in
    [(Subq, [Imm (Lit (Int64.of_int alloc_size)); Reg Rsp]);
      (Movq, [Reg Rsp; lookup layout uid])]

  | Load (ty, operand) ->
    let {tdecls; layout} = ctxt in
    let coperand = [compile_operand ctxt (Reg R11) operand] in
    let temp_reg = (Movq, [Ind2 R11; Reg R10]) in
    let store = (Movq, [Reg R10; lookup layout uid]) in
    coperand @ [temp_reg; store]
  
  | Store (ty, operand1, operand2) ->
    let {tdecls; layout} = ctxt in
    let coperand1 = [compile_operand ctxt (Reg R11) operand1] in
    let coperand2 = [compile_operand ctxt (Reg R10) operand2] in
    let temp_reg = (Movq, [Reg R11; Reg Rax]) in
    let store = (Movq, [Reg Rax; Ind2 R10]) in
    coperand1 @ coperand2 @ [temp_reg; store]

  | Call (ty, operand, args) ->
    let {tdecls; layout} = ctxt in
    begin match operand with
    | Gid g -> compile_call ctxt g args @ [(Movq, [Reg Rax; lookup layout uid])]
    | _ -> failwith "operand should be gid"
    end

  | Bitcast (ty1, operand, ty2) ->
    let {tdecls; layout} = ctxt in
    let coperand = [compile_operand ctxt (Reg R11) operand] in
    let store = (Movq, [Reg R11; lookup layout uid]) in
    coperand @ [store]

  | Gep (ty, operand, path) -> 
    let {tdecls; layout} = ctxt in
    compile_gep ctxt (ty, operand) path @ [(Movq, [Reg R11; lookup layout uid])]


      

| _ -> failwith "unimplemented"



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)

(* terminator:
  | RET t=ty o=operand
    { Ret (t, Some o) }
  | RET t=ty
    { Ret (t, None) }
  | BR LABEL l=UID
    { Br l }
  | BR I1 o=operand COMMA LABEL l1=UID COMMA LABEL l2=UID
    { Cbr (o,l1,l2) } *)


(* Fertig *)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let end_shit = [(Movq, [Reg Rbp; Reg Rsp]); (Popq, [Reg Rbp]); (Retq, [])] in 
  match t with
    | Ret (Void, None) -> end_shit
    | Ret (ty, Some o) -> [compile_operand ctxt (Reg Rax) o] @ end_shit
    (* branch always *)
    | Br lbl -> [(Jmp, [Imm(Lbl(mk_lbl fn lbl))])]
    | Cbr (operand, lbl1, lbl2) ->
      (* wenn gleich null dann ist die evaluation false else true  *)
      let comp = [compile_operand ctxt (Reg R09) operand] in
      comp @ [(Cmpq, [(Imm (Lit 0L)); (Reg R09)]);
        (J Eq, [Imm(Lbl(mk_lbl fn lbl2))]);  (* not sure why but yeah *)
        (Jmp, [Imm(Lbl(mk_lbl fn lbl1))])]
    | _ ->failwith "not fitting terminator"


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
(* insns is uid with instruction ins *)

(* fertig I think *)  
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list = 
  let {insns; term = (uid, terminator)} = blk in 
  let block_code = List.flatten(List.map (fun (uid, insn) -> compile_insn ctxt (uid, insn)) insns) in
  let terminater_code = List.flatten([(compile_terminator fn ctxt terminator)]) in 
  block_code @ terminater_code

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)

(* Mapping the first six arguments to %rdi, %rsi, %rdx, %rcx, %r8, %r9.
Placing additional arguments in stack slots relative to %rbp. *)
(*  1 .. 6:  rdi, rsi, rdx, rcx, r8, r9– 7+: on the stack (in right-to-left order)– Thus, for n > 6,  the nth argument is at  ((n-7)+2)*8 + rb *)
(* WHICH FORMULAR? this or this one: -8 * (n - 5) *)
(* Fertig *)



(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
(* returns layout, which is  (uid * X86.operand)*)
(* TODO *)
let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let gather_uids_from_block (block: Ll.block) =
    let { insns; term = (uid, _) } = block in
    let insn_uids = List.map fst insns in
    uid :: insn_uids
  in
  let entry_uids = gather_uids_from_block block in
  let labeled_uids = List.flatten (List.map (fun (_, blk) -> gather_uids_from_block blk) lbled_blocks) in
  let all_uids = args @ entry_uids @ labeled_uids in
  let unique_uids = List.sort_uniq String.compare all_uids in

  
  let final_layout = List.mapi (fun i uid -> (uid, Ind3 (Lit (Int64.of_int ((i + 1) * -8)), Rbp))) unique_uids in

  final_layout

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)

(* prog is a list of: type elem = { lbl: lbl; global: bool; asm: asm } 
type cfg = block * (lbl * block) list
*)
(* TODO *)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  let name = Platform.mangle name in
  let layout = stack_layout f_param f_cfg in
  let stack_size = 8 * List.length layout in
  let stack_size_aligned =
    if stack_size mod 16 = 0 then stack_size
    else stack_size + (16 - (stack_size mod 16))
  in
  let stack_allocation_amount = Imm (Lit (Int64.of_int stack_size_aligned)) in
  let (block, blocks) = f_cfg in
  let ctxt = { tdecls; layout } in
  let begin_code = [
    (Pushq, [Reg Rbp]);
    (Movq, [Reg Rsp; Reg Rbp]);
    (Subq, [stack_allocation_amount; Reg Rsp])
  ] in
  let arg_moves =
    List.mapi (fun i arg_uid ->
      let src = arg_loc i in
      let dest = lookup layout arg_uid in
      if src = dest then []
      else
      match (src, dest) with
      | (Reg _, _) | (_, Reg _) -> [(Movq, [src; dest])]
      | _ ->
          [ (Movq, [src; Reg R10]); (Movq, [Reg R10; dest]) ]
    ) f_param
  in
  let arg_moves = List.flatten arg_moves in
  
  let entry_block_code = begin_code @ arg_moves @ compile_block name ctxt block in
  let entry_elem = { lbl = name; global = true; asm = Text entry_block_code } in

  let compile_and_label_block (lbl, blk) =
    let block_label = mk_lbl name lbl in
    let block_code = compile_block name ctxt blk in
    { lbl = block_label; global = false; asm = Text block_code }
  in
  let labeled_block_elems = List.map compile_and_label_block blocks in

  entry_elem :: labeled_block_elems



(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
