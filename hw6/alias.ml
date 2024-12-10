(** Alias Analysis *)

open Ll
open Datastructures

(* The lattice of abstract pointers ----------------------------------------- *)
module SymPtr =
  struct
    type t = MayAlias           (* uid names a pointer that may be aliased *)
           | Unique             (* uid is the unique name for a pointer *)
           | UndefAlias         (* uid is not in scope or not a pointer *)

    let compare : t -> t -> int = Pervasives.compare

    let to_string = function
      | MayAlias -> "MayAlias"
      | Unique -> "Unique"
      | UndefAlias -> "UndefAlias"

  end

(* The analysis computes, at each program point, which UIDs in scope are a unique name
   for a stack slot and which may have aliases *)
type fact = SymPtr.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* TASK: complete the flow function for alias analysis. 

   - After an alloca, the defined UID is the unique name for a stack slot
   - A pointer returned by a load, call, bitcast, or GEP may be aliased
   - A pointer passed as an argument to a call, bitcast, GEP, or store
     may be aliased
   - Other instructions do not define pointers

 *)
 let insn_flow ((u, i) : uid * insn) (d : fact) : fact =
  match i with
  | Alloca(ty) -> UidM.add u SymPtr.Unique d
  | Load (ty, op) -> 
    begin match ty with
    | Ptr (Ptr(_)) -> 
        begin match op with
        | Id(src) -> UidM.add u SymPtr.MayAlias d
        | _ -> UidM.add u SymPtr.UndefAlias d
        end
    | _ -> UidM.add u SymPtr.UndefAlias d
    end
  | Call (ty, op, args) ->
      let d_temp =
        match ty with
        | Ptr _ -> UidM.add u SymPtr.MayAlias d
        | _ -> d
      in
      List.fold_left (fun d_ op -> 
        match op with
        | (Ptr(_), Id(src)) -> UidM.add src SymPtr.MayAlias d_
        | _ -> d_
      ) d_temp args
  | Store (ty, op1, op2) -> 
    begin match ty with
    | Ptr (Ptr(_)) -> 
        begin match op2 with
        | Id(src) -> UidM.add src SymPtr.MayAlias d
        | _ ->  UidM.add u SymPtr.UndefAlias d
        end
    | _ -> UidM.add u SymPtr.UndefAlias d
    end
  | Bitcast (ty1, op, ty2) ->
    let d_temp = begin match ty1 with
    | Ptr(_) -> UidM.add u SymPtr.MayAlias d
    | _ -> d
    end in 
    begin match ty2 with
    | Ptr(_) ->
      begin match op with
      | Id(src) -> UidM.add src SymPtr.MayAlias d_temp
      end
    | _ -> d_temp
    end
  | Gep (ty, ptr, _) ->
    begin match ty with
    | Ptr(_) -> 
        begin match ptr with
        | Id(src) -> UidM.add src SymPtr.MayAlias (UidM.add u SymPtr.MayAlias d)
        | _ -> UidM.add u SymPtr.MayAlias d
        end
    | _ -> UidM.add u SymPtr.MayAlias d
    end
  
  | _ -> UidM.add u SymPtr.UndefAlias d


(* The flow function across terminators is trivial: they never change alias info *)
let terminator_flow t (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    (* UndefAlias is logically the same as not having a mapping in the fact. To
       compare dataflow facts, we first remove all of these *)
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymPtr.UndefAlias)

    let compare (d:fact) (e:fact) : int = 
      UidM.compare SymPtr.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

    (* TASK: complete the "combine" operation for alias analysis.

       The alias analysis should take the join over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful.

       It may be useful to define a helper function that knows how to take the
       join of two SymPtr.t facts.
    *)
    let combine (ds: fact list) : fact =
      let merge_helper key v1 v2 =
        match (v1, v2) with
        | (Some SymPtr.MayAlias, _) | (_, Some SymPtr.MayAlias) -> Some SymPtr.MayAlias
        | (Some SymPtr.Unique, Some SymPtr.Unique) -> Some SymPtr.Unique
        | (Some SymPtr.Unique, None) | (None, Some SymPtr.Unique) -> Some SymPtr.Unique
        | (None, None) -> None
        | (Some SymPtr.UndefAlias, _) | (_, Some SymPtr.UndefAlias) -> Some SymPtr.UndefAlias
      in
      List.fold_left (fun acc ds ->
        UidM.merge merge_helper acc ds
      ) UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefAlias *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any pointer parameter 
     to the function may be aliased *)
  let alias_in = 
    List.fold_right 
      (fun (u,t) -> match t with
                    | Ptr _ -> UidM.add u SymPtr.MayAlias
                    | _ -> fun m -> m) 
      g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init alias_in g in
  Solver.solve fg

