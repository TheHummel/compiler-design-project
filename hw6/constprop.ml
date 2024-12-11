open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
 let insn_flow (u, i : uid * insn) (d : fact) : fact = 
  let calc_op op fact_map =
    match op with
    | Const c -> SymConst.Const c
    | Id id -> (
      match UidM.find_opt id fact_map with
      | Some s -> s
      | None -> SymConst.UndefConst)
    | _ -> SymConst.NonConst
  in
  let calc_binop binop val1 val2 =
    match binop with
    | Add -> Int64.add val1 val2
    | Sub -> Int64.sub val1 val2
    | Mul -> Int64.mul val1 val2
    | Shl -> Int64.shift_left val1 (Int64.to_int val2)
    | Lshr -> Int64.shift_right_logical val1 (Int64.to_int val2)
    | Ashr -> Int64.shift_right val1 (Int64.to_int val2)
    | And -> Int64.logand val1 val2
    | Or -> Int64.logor val1 val2
    | Xor -> Int64.logxor val1 val2
  in
  let calc_res op state1 state2 =
    match (state1, state2) with
    | SymConst.Const val1, SymConst.Const val2 -> SymConst.Const (calc_binop op val1 val2)
    | SymConst.UndefConst, _ | _, SymConst.UndefConst -> SymConst.UndefConst
    | _ -> SymConst.NonConst
  in
  let compare comparator val1 val2 =
    let res = match comparator with
      | Eq -> Int64.equal val1 val2
      | Ne -> not (Int64.equal val1 val2)
      | Slt -> Int64.compare val1 val2 < 0
      | Sle -> Int64.compare val1 val2 <= 0
      | Sgt -> Int64.compare val1 val2 > 0
      | Sge -> Int64.compare val1 val2 >= 0
    in
    if res then 1L else 0L
  in
  let calc_compare cmp state1 state2 =
    match (state1, state2) with
    | SymConst.Const val1, SymConst.Const val2 -> SymConst.Const (compare cmp val1 val2)
    | SymConst.UndefConst, _ | _, SymConst.UndefConst -> SymConst.UndefConst
    | _ -> SymConst.NonConst
  in
  
  let res =
    match i with
    | Binop (opcode, _, op1, op2) ->
        calc_res opcode (calc_op op1 d) (calc_op op2 d)
    | Icmp (cmp, _, op1, op2) ->
        calc_compare cmp (calc_op op1 d) (calc_op op2 d)
    | Store _ | Call (Void, _, _) -> SymConst.UndefConst
    | Alloca _ | Load _ | Bitcast _ | Gep _ | Call _ -> SymConst.NonConst
  in

  UidM.add u res d


(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = (* jannis not todo I think its fine *)
      let open SymConst in
      match ds with
      | [] -> UidM.empty
      | [d] -> d
      | _ -> 
        List.fold_left (fun acc d ->
          UidM.merge (fun _k v1 v2 ->
            match (v1, v2) with
            | (Some Const x, Some Const y) -> if x = y then Some (Const x) else Some NonConst
            | (Some UndefConst, Some x) -> Some x
            | (Some x, Some UndefConst) -> Some x
            | (Some(Const x), _) -> Some(Const x)
            | (_, Some(Const y)) -> Some(Const y)
            | (Some(UndefConst), y) -> y
            | (x, Some(UndefConst)) -> x
            | _ -> Some NonConst
          ) acc d
        ) (List.hd ds) (List.tl ds)

  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in

  let resolve_op (map: SymConst.t UidM.t) (op: Ll.operand) : Ll.operand =
    match op with
    | Ll.Id uid -> (
        match UidM.find_opt uid map with
        | Some (Const value) -> Ll.Const value
        | _ -> op
      )
    | _ -> op
  in
  let new_insn (map: SymConst.t UidM.t) ((uid, insn): Ll.uid * Ll.insn) : Ll.uid * Ll.insn =
    let new_insn_ =
      match insn with
      | Binop (bop, ty, op1, op2) ->
          Binop (bop, ty, resolve_op map op1, resolve_op map op2)
      | Icmp (cond, ty, op1, op2) ->
          Icmp (cond, ty, resolve_op map op1, resolve_op map op2)
      | Load (ty, op) ->
          Load (ty, resolve_op map op)
      | Store (ty, op1, op2) ->
          Store (ty, resolve_op map op1, resolve_op map op2)
      | Call (ty, op, args) ->
          Call (ty, resolve_op map op, List.map (fun (t, o) -> (t, resolve_op map o)) args)
      | Gep (ty, base, indices) ->
          Gep (ty, resolve_op map base, List.map (resolve_op map) indices)
      | Bitcast (ty1, op, ty2) ->
          Bitcast (ty1, resolve_op map op, ty2)
      | _ -> insn
    in
    (uid, new_insn_)
  in
  let new_terminator (map: SymConst.t UidM.t) ((uid, term): Ll.uid * Ll.terminator) : Ll.uid * Ll.terminator =
    let rewritten_term =
      match term with
      | Ret (ty, Some op) -> Ret (ty, Some (resolve_op map op))
      | Cbr (op, lbl1, lbl2) -> Cbr (resolve_op map op, lbl1, lbl2)
      | _ -> term
    in
    (uid, rewritten_term)
  in

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in

    let { insns; term } = b in
    let new_insns =
      List.map (fun (uid, insn) ->
        let map = cb uid in
        new_insn map (uid, insn)
      ) insns
    in

    let (term_uid, _) = term in
    let term_map = cb term_uid in
    let new_term = new_terminator term_map term in

    { cfg with blocks=LblM.add l { insns = new_insns; term = new_term } cfg.blocks }
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
