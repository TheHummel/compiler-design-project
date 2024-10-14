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


let get_mem_val (mem: mem) (addr: int64) : int64 =
  if addr < mem_bot || Int64.add addr 7L > mem_top then failwith "out of bounds";
  let addr_int = 
    match map_addr addr with
    | Some v -> v
    | None -> failwith "invalid address"
  in
  let rec read_bytes n acc shift =
    if n = 8 then acc
    else match mem.(addr_int + n) with
      | Byte b -> read_bytes (n + 1) (Int64.logor acc (Int64.shift_left (Int64.of_int (Char.code b)) shift)) (shift + 8)
      | _ -> raise X86lite_segfault
  in
  read_bytes 0 0L 0


let set_mem_val (mem: mem) (addr: int64) (value: int64) : unit =
  if addr < mem_bot || Int64.add addr 7L > mem_top then failwith "out of bounds";
  let addr_int = 
    match map_addr addr with
    | Some v -> v
    | None -> failwith "invalid address"
  in
  for i = 0 to 7 do
    let byte = Char.chr (Int64.to_int (Int64.shift_right value (i * 8)) land 0xFF) in
    match mem.(addr_int + i) with
    | Byte _ -> mem.(addr_int + i) <- Byte byte
    | _ -> raise X86lite_segfault
  done

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let rip = Array.get m.regs (rind Rip) in
  let rip_idx = 
      match map_addr rip with
      | Some idx -> idx
      | None -> raise X86lite_segfault
  in
  let instruction = Array.get m.mem rip_idx in
  begin match instruction with
  | InsB0 ins ->
    let (opcode, operands) = ins in
    begin match opcode with
    | Incq | Decq | Negq | Notq -> 
      begin match operands with
      | op1::[] -> 
        let dest_val =
          begin match interp_opnd op1 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let new_val =
          begin match opcode with
          | Incq -> Int64.succ dest_val
          | Decq -> Int64.pred dest_val
          | Negq -> Int64.neg dest_val
          | Notq -> Int64.lognot dest_val
          end
        in
        begin match interp_opnd op1 m with
        | Value _ -> 
          let reg_idx = rind (match op1 with Reg r -> r | _ -> failwith "no register") in
          Array.set m.regs reg_idx new_val
        | MemLoc addr ->
          set_mem_val m.mem addr new_val
        end
      | _ -> failwith ""
      end
    | Addq | Subq | Imulq | Xorq | Orq | Andq -> 
      begin match operands with
      | [op1; op2] ->
        let src_val =
          begin match interp_opnd op1 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let dest_val =
          begin match interp_opnd op2 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let new_val = 
          begin match opcode with
          | Addq -> Int64.add src_val dest_val
          | Subq -> Int64.sub src_val dest_val
          | Imulq -> Int64.mul src_val dest_val
          | Xorq -> Int64.logxor src_val dest_val
          | Orq -> Int64.logor src_val dest_val
          | Andq -> Int64.logand src_val dest_val
          end
        in
        begin match interp_opnd op2 m with
        | Value _ -> 
          let reg_idx = rind (match op2 with Reg r -> r | _ -> failwith "no register") in
          Array.set m.regs reg_idx new_val
        | MemLoc addr ->
          set_mem_val m.mem addr new_val
        end
      | _ -> ()
      end
    | Leaq ->
      begin match operands with
      | [op1; op2] -> 
        let addr =
          match interp_opnd op1 m with
          | MemLoc addr -> addr
          | Value _ -> failwith "Leaq source should be an address"
        in
        begin match op2 with
        | Reg reg ->
          let reg_idx = rind reg in
          Array.set m.regs reg_idx addr
        | _ -> failwith "Leaq dest should be a register"
        end
      | _ -> ()
      end
    | Shlq | Sarq | Shrq -> 
      begin match operands with
      | [op1; op2] ->
        let amt =
          begin match interp_opnd op1 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let dest_val =
          begin match interp_opnd op2 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let new_val = 
          match opcode with
          | Shlq -> Int64.shift_left dest_val (Int64.to_int amt)
          | Sarq -> Int64.shift_right dest_val (Int64.to_int amt)
          | Shrq -> Int64.shift_right_logical dest_val (Int64.to_int amt)
        in
        begin match interp_opnd op2 m with
        | Value _ -> 
          let reg_idx = rind (match op2 with Reg r -> r | _ -> failwith "no register") in
          Array.set m.regs reg_idx new_val
        | MemLoc addr ->
          set_mem_val m.mem addr new_val
        end
      | _ -> ()
      end
    | Movq | Pushq | Popq ->
      begin match opcode with
      | Movq ->
        begin match operands with
        | [op1; op2] ->
          let src_val =
            begin match interp_opnd op1 m with
            | Value v -> v
            | MemLoc addr -> get_mem_val m.mem addr
            end
          in
          begin match interp_opnd op2 m with
          | Value _ -> 
            let reg_idx = rind (match op2 with Reg r -> r | _ -> failwith "no register") in
            Array.set m.regs reg_idx src_val
          | MemLoc addr ->
            set_mem_val m.mem addr src_val
          end
        | _ -> ()
        end
      | Pushq ->
        begin match operands with
        | [op1] ->
          let src_val =
            begin match interp_opnd op1 m with
            | Value v -> v
            | MemLoc addr -> get_mem_val m.mem addr
            end
          in
          let rsp_index = rind Rsp in
          let rsp_val = Array.get m.regs rsp_index in
          let new_rsp = Int64.sub rsp_val 8L in
          Array.set m.regs rsp_index new_rsp;

          set_mem_val m.mem new_rsp src_val
        | _ -> ()
        end
      | Popq ->
        begin match operands with
        | [op1] ->
          let rsp_index = rind Rsp in
          let rsp_val = Array.get m.regs rsp_index in
          let mem_rsp = get_mem_val m.mem rsp_val in

          let new_rsp = Int64.add rsp_val 8L in
          Array.set m.regs rsp_index new_rsp;

          begin match op1 with
          | Reg reg ->
            let reg_idx = rind reg in
            Array.set m.regs reg_idx mem_rsp
          | _ -> failwith "dest must be a register"
          end
        end
      end
    | Jmp ->
      begin match operands with
      | [op1] ->
        let src_val =
          begin match interp_opnd op1 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let rip_index = rind Rip in
        Array.set m.regs rip_index src_val

      end
          
    | J cnd ->
      begin match operands with
      | [op1] ->
        let src_val =
          begin match interp_opnd op1 m with
          | Value v -> v
          | MemLoc addr -> get_mem_val m.mem addr
          end
        in
        let rip_index = rind Rip in

        if interp_cnd m.flags cnd then
          Array.set m.regs rip_index src_val
        else () (* Todo *)
      end

    | Cmpq ->
      begin match opcode with
      | Cmpq ->
        match operands with
        | [op1; op2] ->
          let src_val1 =
            begin match interp_opnd op1 m with
            | Value v -> v
            | MemLoc addr -> get_mem_val m.mem addr
            end
          in
          let src_val2 =
            begin match interp_opnd op2 m with
            | Value v -> v
            | MemLoc addr -> get_mem_val m.mem addr
            end
          in
          m.flags.fs <- src_val1 < src_val2;
          m.flags.fz <- src_val1 = src_val2;
          (* Todo *)

        | _ -> ()
        
      (* | Set cnd *)
      | _ -> ()
        end
    | Callq | Retq ->
      let rip_idx = rind Rip in
      let rsp_idx = rind Rsp in
      let rip_val = Array.get m.regs rip_idx in
      let rsp_val = Array.get m.regs rsp_idx in

      match opcode with
      | Callq ->
        begin match operands with
        | [op1] -> 
          let new_rsp = Int64.sub rsp_val 8L in
          Array.set m.regs rsp_idx new_rsp;
    
          set_mem_val m.mem new_rsp rip_val;
    
          let new_rip =
            match interp_opnd op1 m with
            | Value addr -> addr
            | MemLoc addr -> get_mem_val m.mem addr
          in
          Array.set m.regs rip_idx new_rip;
        | _ -> ()
        end

      | Retq ->
        let return_addr = get_mem_val m.mem rsp_val in
        let new_rsp = Int64.add rsp_val 8L in
        Array.set m.regs rsp_idx new_rsp;
        Array.set m.regs rip_idx return_addr;


    end

  | InsFrag -> ()
  | Byte char -> ()
  
  end

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
failwith "assemble unimplemented"

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
failwith "load unimplemented"
