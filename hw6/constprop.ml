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
 let insn_flow (u, i : uid * insn) (d : fact) : fact = (* Jannis pls look at this TODO *)
  let resolve_operand op fact_map =
    match op with
    | Const v -> SymConst.Const v
    | Id id -> (
      match UidM.find_opt id fact_map with
      | Some v -> v
      | None -> SymConst.UndefConst)
    | _ -> SymConst.NonConst
  in
  let comp_res op state1 state2 =
    match (state1, state2) with
    | (SymConst.Const v1, SymConst.Const v2) -> (
        match op with
        | Add -> SymConst.Const (Int64.add v1 v2)
        | Sub -> SymConst.Const (Int64.sub v1 v2)
        | Mul -> SymConst.Const (Int64.mul v1 v2)
        | Shl -> SymConst.Const (Int64.shift_left v1 (Int64.to_int v2))
        | Lshr -> SymConst.Const (Int64.shift_right_logical v1 (Int64.to_int v2))
        | Ashr -> SymConst.Const (Int64.shift_right v1 (Int64.to_int v2))
        | And -> SymConst.Const (Int64.logand v1 v2)
        | Or -> SymConst.Const (Int64.logor v1 v2)
        | Xor -> SymConst.Const (Int64.logxor v1 v2))
    | (SymConst.UndefConst, _) | (_, SymConst.UndefConst) -> SymConst.UndefConst
    | _ -> SymConst.NonConst
  in
  let comp_cmp cmp state1 state2 =
    match (state1, state2) with
    | (SymConst.Const v1, SymConst.Const v2) -> (
        match cmp with
        | Eq -> SymConst.Const (if Int64.equal v1 v2 then 1L else 0L)
        | Ne -> SymConst.Const (if Int64.equal v1 v2 then 0L else 1L)
        | Slt -> SymConst.Const (if Int64.compare v1 v2 < 0 then 1L else 0L)
        | Sle -> SymConst.Const (if Int64.compare v1 v2 <= 0 then 1L else 0L)
        | Sgt -> SymConst.Const (if Int64.compare v1 v2 > 0 then 1L else 0L)
        | Sge -> SymConst.Const (if Int64.compare v1 v2 >= 0 then 1L else 0L))
    | (SymConst.UndefConst, _) | (_, SymConst.UndefConst) -> SymConst.UndefConst
    | _ -> SymConst.NonConst
  in
  let result =
    begin match i with
    | Binop (op, _, op1, op2) ->
        let state1 = resolve_operand op1 d in
        let state2 = resolve_operand op2 d in
        comp_res op state1 state2
    | Icmp (cmp, _, op1, op2) ->
        let state1 = resolve_operand op1 d in
        let state2 = resolve_operand op2 d in
        comp_cmp cmp state1 state2
    | Store _ | Call (Void, _, _) -> SymConst.UndefConst
    | Alloca _ | Load _ | Bitcast _ | Gep _ | Call _ -> SymConst.NonConst end
  in
  UidM.add u ( result) d


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
            | (Some Const x, Some Const y) when x = y -> Some (Const x)
            | (Some UndefConst, Some x) -> Some x
            | (Some x, Some UndefConst) -> Some x
            | (Some(Const x), _) -> Some(SymConst.Const x)
            | (_, Some(SymConst.Const y)) -> Some(SymConst.Const y)
            | (Some(SymConst.UndefConst), y) -> y
            | (x, Some(SymConst.UndefConst)) -> x
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
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    failwith "Constprop.cp_block unimplemented"
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
