(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* Helper functions for setting flags *)
let flag_set_sign flags result =
  flags.fs <- (Int64.shift_right result 63) <> 0L

let flag_set_zero flags result =
  flags.fz <- result = 0L


let flag_set_shl flags dest_val amt result =
  if (amt <> 0L) then begin
    flag_set_zero flags result;
    flag_set_sign flags result;
  end;
  if (amt = 1L) then 
    flags.fo <- (Int64.logxor (Int64.shift_right dest_val 63) (Int64.shift_right dest_val 62) <> 0L)

let flag_set_shr flags dest_val amt result =
  if (amt <> 0L) then begin  
    flags.fs <- (Int64.shift_right result 63 <> 0L);
    flag_set_zero flags result;
  end;
  if (amt = 1L) then 
    flags.fo <- (Int64.shift_right dest_val 63 <> 0L)

let flag_set_sar flags amt result =  
  if (amt <> 0L) then begin
    flag_set_zero flags result;
    flag_set_sign flags result;
  end; 
  if (amt = 1L) then 
    flags.fo <- false

let flag_set_logic flags result =
  flags.fo <- false;
  flag_set_sign flags result;
  flag_set_zero flags result


let flag_set_neg flags dest_val result =
  flags.fo <- (dest_val = Int64.min_int);
  flag_set_sign flags result;
  flag_set_zero flags result

let flag_set_add flags result =
  flag_set_sign flags result;
  flag_set_zero flags result

let flag_set_sub flags result =
  flag_set_sign flags result;
  flag_set_zero flags result
  
let flag_set_sign flags result =
  flags.fs <- (Int64.shift_right result 63) <> 0L

let flag_set_zero flags result =
  flags.fz <- result = 0L


let flag_set_imulq flags dest_val src_val =
  let result_with_overflow = Int64_overflow.mul dest_val src_val in
  flags.fo <- result_with_overflow.overflow


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = 
  fun x -> 
    begin match x with
    | Eq -> fz
    | Neq -> not fz
    | Gt -> fs = fo && not fz
    | Ge -> fs = fo
    | Lt -> fs != fo
    | Le -> fs != fo || fz
    end
    
(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if Int64.compare addr mem_bot >= 0 && Int64.compare addr mem_top < 0 then
    Some (Int64.to_int addr - Int64.to_int mem_bot)
  else
    None




type opnd_val =
  | Value of int64
  | MemLoc of int64

let interp_opnd (op: operand) (m: mach) : opnd_val =
  match op with
  | Imm (Lit v) -> Value v
  | Imm (Lbl _) -> failwith "Label not supported"
  | Reg reg -> Value (Array.get m.regs (rind reg))
  | Ind1 (Lit imm) -> MemLoc imm
  | Ind1 (Lbl _) -> failwith "Label not supported"
  | Ind2 reg -> 
    let addr = Array.get m.regs (rind reg) in
    MemLoc addr
  | Ind3 (Lit disp, reg) -> 
    let base = Array.get m.regs (rind reg) in
    MemLoc (Int64.add disp base)
  | Ind3 (Lbl _, _) -> failwith "Label not supported"



let read_from_operand (m:mach) (operand:operand) : int64 =
  let read_mem addr =
    match map_addr addr with
    | Some index ->
      let bytes = Array.sub m.mem index 8 in
      int64_of_sbytes (Array.to_list bytes)
    | None -> raise X86lite_segfault
  in
  match operand with
  | Imm (Lit value) -> value
  | Reg reg -> m.regs.(rind reg)
  | Ind1 (Lit addr) -> read_mem addr
  | Ind2 reg -> read_mem m.regs.(rind reg)
  | Ind3 (Lit disp, reg) -> read_mem (Int64.add disp m.regs.(rind reg))
  | _ -> failwith "Invalid operand"

let write_to_operand (m:mach) (operand:operand) (value:int64) : unit =
  let write_mem addr =
    match map_addr addr with
    | Some index ->
      let bytes = Array.of_list (sbytes_of_int64 value) in
      Array.blit bytes 0 m.mem index 8
    | None -> raise X86lite_segfault
  in
  match operand with
  | Reg reg -> m.regs.(rind reg) <- value
  | Ind1 (Lit addr) -> write_mem addr
  | Ind2 reg -> write_mem m.regs.(rind reg)
  | Ind3 (Lit disp, reg) -> write_mem (Int64.add disp m.regs.(rind reg))
  | _ -> failwith "Invalid operand"


(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let rip = m.regs.(rind Rip) in
  let rip_index =
    match map_addr rip with
    | Some idx -> idx
    | None -> raise X86lite_segfault
  in
  let instruction =
    match m.mem.(rip_index) with
    | InsB0 ins -> ins
    | _ -> raise X86lite_segfault
  in
  let (opcode, operands) = instruction in
  let rip_modified = ref false in

  let update_flags_arith result overflow =
    m.flags.fo <- overflow;
    m.flags.fs <- Int64.shift_right result 63 <> 0L;
    m.flags.fz <- result = 0L
  in


  begin match opcode with
  | Incq | Decq | Negq | Notq ->
    begin match operands with
    | [dst] ->
      let dest_val = read_from_operand m dst in
      begin match opcode with
      | Incq ->
  
        let result_with_overflow = Int64_overflow.succ dest_val in
        update_flags_arith result_with_overflow.value result_with_overflow.overflow;
        write_to_operand m dst result_with_overflow.value
      | Decq ->
        let result_with_overflow = Int64_overflow.pred dest_val in
        update_flags_arith result_with_overflow.value result_with_overflow.overflow;
        write_to_operand m dst result_with_overflow.value

      | Negq ->
        let result_with_overflow = Int64_overflow.neg dest_val in
        update_flags_arith result_with_overflow.value result_with_overflow.overflow;
        write_to_operand m dst result_with_overflow.value
      | Notq ->
        let result = Int64.lognot dest_val in
        (* update_flags_logic result; *)
        write_to_operand m dst result
      end
    | _ -> failwith "Invalid operands"
    end
  | Addq | Subq | Imulq | Xorq | Orq | Andq ->
    begin match operands with
    | [src; dst] ->
      let src_val = read_from_operand m src in
      let dest_val = read_from_operand m dst in
      begin match opcode with
      | Addq ->
        
        let result_with_overflow = Int64_overflow.add dest_val src_val in
        update_flags_arith result_with_overflow.value result_with_overflow.overflow;
        write_to_operand m dst result_with_overflow.value
      | Subq ->
        let result_with_overflow = Int64_overflow.sub dest_val src_val in
        update_flags_arith result_with_overflow.value result_with_overflow.overflow;
        write_to_operand m dst result_with_overflow.value
      | Imulq ->
        let result = Int64.mul dest_val src_val in
        flag_set_imulq m.flags dest_val src_val;
        write_to_operand m dst result
      | Andq ->
        let result = Int64.logand dest_val src_val in
        flag_set_logic m.flags result;
        write_to_operand m dst result
      | Xorq ->
        let result = Int64.logxor dest_val src_val in
        flag_set_logic m.flags result;
        write_to_operand m dst result
      | Orq ->
        let result = Int64.logor dest_val src_val in
        flag_set_logic m.flags result;
        write_to_operand m dst result
      end
    | _ -> failwith "Invalid operands"
    end
  | Shlq | Sarq | Shrq ->
    begin match operands with
    | [amt; dst] ->
      let amt_val = read_from_operand m amt in
      let dest_val = read_from_operand m dst in
      begin match opcode with
      | Shlq ->
        let result = Int64.shift_left dest_val (Int64.to_int amt_val) in
        flag_set_shl m.flags dest_val amt_val result;
        write_to_operand m dst result
      | Sarq ->
        let result = Int64.shift_right dest_val (Int64.to_int amt_val) in
        flag_set_sar m.flags amt_val result;
        write_to_operand m dst result
      | Shrq ->
        let result = Int64.shift_right_logical dest_val (Int64.to_int amt_val) in
        flag_set_shr m.flags dest_val amt_val result;
        write_to_operand m dst result
      end
    | _ -> failwith "Invalid operands"
    end
  | Leaq ->
    begin match operands with
    | [src; dst] ->
      let src_val = 
        match src with
        | Ind1 (Lit addr) -> addr
        | Ind2 reg -> m.regs.(rind reg)
        | Ind3 (Lit base, offset) -> Int64.add base m.regs.(rind offset)
        | _ -> failwith "Invalid operand"
      in
      (* let src_val = read_from_operand m src in *)
      write_to_operand m dst src_val
    | _ -> failwith "Invalid operands"
    end
  | Movq | Pushq | Popq ->
    begin match opcode with
    | Movq ->
      begin match operands with
      | [src; dst] ->
          let src_val = read_from_operand m src in
          write_to_operand m dst src_val
      | _ -> failwith "Invalid operands"
      end
    | Pushq ->
      begin match operands with
      | [src] ->
          let src_val = read_from_operand m src in
          let rsp = m.regs.(rind Rsp) in
          m.regs.(rind Rsp) <- Int64.sub rsp 8L;
          write_to_operand m (Ind2 Rsp) src_val
      | _ -> failwith "Invalid operands"
      end
    | Popq ->
      begin match operands with
      | [op1] ->
          let rsp = m.regs.(rind Rsp) in
          let op1_val = read_from_operand m (Ind2 Rsp) in
          m.regs.(rind Rsp) <- Int64.add rsp 8L;
          write_to_operand m op1 op1_val
      | _ -> failwith "Invalid operands"
      end
    end
  | Jmp | J _ ->
    begin match opcode with
    | Jmp ->
      begin match operands with
      | [op1] ->
          let target = read_from_operand m op1 in
          m.regs.(rind Rip) <- target;
          rip_modified := true
      | _ -> failwith "Invalid operands"
      end
    | J cnd ->
      begin match operands with
      | [op1] ->
          if interp_cnd m.flags cnd then
            let target = read_from_operand m op1 in
            m.regs.(rind Rip) <- target;
            rip_modified := true
      | _ -> failwith "Invalid operands"
      end
    end
  | Cmpq  | Set _ ->
    begin match opcode with
    | Cmpq ->
      begin match operands with
      | [op1; op2] ->
          let op1_val = read_from_operand m op1 in
          let op2_val = read_from_operand m op2 in
          let result_with_overflow = Int64_overflow.sub op2_val op1_val in
          update_flags_arith result_with_overflow.value result_with_overflow.overflow;
      | _ -> failwith "Invalid operands"
      end
    | Set cnd ->
      begin match operands with
      | [src] ->
          let src_val = read_from_operand m src in
          let cnd_result = interp_cnd m.flags cnd in
          let lower_byte = if cnd_result then 1L else 0L in
          let mask = Int64.logand src_val 0xFFFFFFFFFFFFFF00L in
          let result = Int64.logor mask lower_byte in
          write_to_operand m src result
      | _ -> failwith "Invalid operands"
      end
    end
  | Callq | Retq ->
    begin match opcode with
    | Callq ->
        begin match operands with
        | [op1] ->
            let target = read_from_operand m op1 in
            let rsp = m.regs.(rind Rsp) in
            m.regs.(rind Rsp) <- Int64.sub rsp 8L;
            write_to_operand m (Ind2 Rsp) (Int64.add rip 8L);
            m.regs.(rind Rip) <- target;
            rip_modified := true
        | _ -> failwith "Invalid operands"
        end
    | Retq ->
        let rsp = m.regs.(rind Rsp) in
        let return_addr = read_from_operand m (Ind2 Rsp) in
        m.regs.(rind Rsp) <- Int64.add rsp 8L;
        m.regs.(rind Rip) <- return_addr;
        rip_modified := true
    end
  | _ -> failwith "opcode not supported"
end;

if not !rip_modified then
  m.regs.(rind Rip) <- Int64.add rip ins_size


  

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
  let initial_exec = { entry = 0x400000L; text_pos = 0x400000L; data_pos = 0x400000L; text_seg = []; data_seg = [] } in
  let label_table : (lbl, quad) Hashtbl.t = Hashtbl.create 10 in
  let curr_text_addr = ref initial_exec.text_pos in
  let main_found = ref false in
  let entry_addr = ref initial_exec.entry in
  (* Map instr labels *)
  List.iter (fun elem ->
    let {lbl; global; asm} = elem in
    begin match asm with
    | Text instr_list ->
      if Hashtbl.mem label_table lbl then raise (Redefined_sym lbl);
      if lbl = "main" then begin
        main_found := true;
        entry_addr := !curr_text_addr;
      end;
      Hashtbl.add label_table lbl !curr_text_addr;
      curr_text_addr := Int64.add !curr_text_addr (Int64.of_int (8 * List.length instr_list));
    | Data data_list -> ()
    end

  ) p;
  if not !main_found then raise (Undefined_sym "main");
  let updated_exec = { initial_exec with 
    entry = !entry_addr;
    data_pos = !curr_text_addr;
  } in
  (* Map data labels *)
  let curr_data_addr = ref !curr_text_addr in
  List.iter (fun elem ->
    let {lbl; global; asm} = elem in
    match asm with
    | Text instr_list -> ()
    | Data data_list ->
      if Hashtbl.mem label_table lbl then raise (Redefined_sym lbl);
      Hashtbl.add label_table lbl !curr_data_addr;
      let data_size = List.fold_left (fun acc data_elem ->
        match data_elem with
        | Quad _ -> acc + 8
        | Asciz s -> acc + String.length s + 1
      ) 0 data_list in
      curr_data_addr := Int64.add !curr_data_addr (Int64.of_int data_size)
  ) p;
  (* populate text and data segment *)
  List.fold_left (fun acc elem ->
    let {lbl; global; asm} = elem in
    match asm with
    | Text instrs -> 
      List.fold_left (fun acc ins ->
        let (opcode, operands) = ins in
        let new_operands = List.map (fun op ->
          begin match op with
          | Imm (Lbl l) -> 
            if not (Hashtbl.mem label_table l) then raise (Undefined_sym l);
            Imm (Lit (Hashtbl.find label_table l))
          | Imm (Lit l) -> Imm (Lit l)
          | Ind1 (Lbl l) -> 
            if not (Hashtbl.mem label_table l) then raise (Undefined_sym l);
            Ind1 (Lit (Hashtbl.find label_table l))
          | Ind3 (Lbl l, reg) -> 
            if not (Hashtbl.mem label_table l) then raise (Undefined_sym l);
            Ind3 (Lit (Hashtbl.find label_table l), reg)
          | _ -> op
          end
        ) operands
        in
        let text_seg = acc.text_seg @ sbytes_of_ins (opcode, new_operands) in
          { acc with text_seg } 
      ) acc instrs
    | Data data ->
      List.fold_left (fun acc d ->
        let data_seg = acc.data_seg @ sbytes_of_data d in
        { acc with data_seg }
      ) acc data
  ) updated_exec p

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach =
  let mem = Array.make mem_size (Byte '\x00') in
  let text_length = List.length text_seg in
  let data_length = List.length data_seg in
  let text_array = Array.of_list text_seg in
  let data_array = Array.of_list data_seg in
  Array.blit text_array 0 mem 0 text_length;
  let mem_start = Int64.to_int data_pos - Int64.to_int mem_bot in
  Array.blit data_array 0 mem mem_start data_length;

  Array.blit (Array.of_list (sbytes_of_int64 exit_addr)) 0 mem (mem_size - 8) 8;
  
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- Int64.sub mem_top 8L;

  { flags = {fo = false; fs = false; fz = false};
    regs = regs;
    mem = mem
  }

