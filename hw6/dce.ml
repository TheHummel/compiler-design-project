(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
 let dce_block (lb:uid -> Liveness.Fact.t) (ab:uid -> Alias.fact) (b:Ll.block) : Ll.block =
    let { insns; term } = b in
    let is_live inst uid =
    match inst with
    | Call(_, _, _) -> true
    | Store(_, _, Id dest) ->
      let bool_is_live = match UidS.find_opt dest (lb uid) with
        | Some _ -> true
        | None -> false
      in
      let bool_is_there = match UidM.find_opt dest (ab uid) with
        | Some Alias.SymPtr.MayAlias -> true
        | _ -> false
      in
      (bool_is_live || bool_is_there)
    | Store(_, _, _) -> true
    | _ -> 
      match UidS.find_opt uid (lb uid) with
        | Some s -> true
        | None -> false
    in
    let filtered_insns = List.filter (fun (uid, ins) ->
      is_live ins uid
    ) insns 
    in
    let block = { insns = filtered_insns; term = term }
    in 
    block


let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

