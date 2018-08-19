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
   'symbolic instructions' that take up four bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
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
           | InsFrag            (* 2nd - 7th bytes of an instruction *)
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
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"

(* It might be useful to toggle printing of intermediate states of your 
   simulator. *)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
  | Eq -> fz
  | Neq -> not fz
  | Gt -> not ((fo != fs) || fz )
  | Ge -> not (fs != fo)
  | Lt -> fs != fo
  | Le -> (fo != fs) || fz

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if (Int64.compare addr mem_top) = -1 && not ((Int64.compare addr mem_bot) = -1)
  then Some(Int64.to_int(Int64.sub addr mem_bot))
  else None

let reg_val (m:mach) (r: reg): int64 =
  Array.get m.regs (rind r)

exception OutOfBounds
let addr_start_index (addr: int64): int =
  match (map_addr addr) with
  | None -> raise OutOfBounds
  | Some(index) -> index

let read_8_bytes_from_mem (m: mach) (start_index: int): sbyte list =
  let sbytes_array = Array.sub m.mem start_index 8 in
  Array.to_list sbytes_array

exception UnresolvedLabel
let read = fun m addr ->
  match addr with
  | Imm Lbl _ -> raise UnresolvedLabel
  | Imm Lit quad -> sbytes_of_int64 quad
  | Reg reg -> (
    let reg_val = reg_val m reg in
    sbytes_of_int64 reg_val
  )
  | Ind1 Lbl _ -> raise UnresolvedLabel
  | Ind1 Lit ind_addr -> (
    let start_index = addr_start_index ind_addr in
    let addr_sbytes = read_8_bytes_from_mem m start_index in
    let addr = int64_of_sbytes addr_sbytes in
    let start_index = addr_start_index addr in
    read_8_bytes_from_mem m start_index
  )
  | Ind2 reg -> (
    let reg_val = reg_val m reg in
    let start_index = addr_start_index reg_val in
    read_8_bytes_from_mem m start_index
  )
  | Ind3 (Lbl _, reg) -> raise UnresolvedLabel
  | Ind3 (Lit offset, reg) -> (
    let reg_val = reg_val m reg in
    let index = addr_start_index reg_val in
    let start_index = index + Int64.to_int offset in
    read_8_bytes_from_mem m start_index
  )

let write_8_bytes_to_mem = fun m start_index sbytes ->
  let aux = fun ind sb -> Array.set m.mem (start_index + ind) sb in
  List.iteri aux sbytes

let write = fun m addr data ->
  match addr with
  | Imm Lbl _ -> raise UnresolvedLabel
  | Imm Lit _ -> ()
  | Reg reg -> (
    let data_int64 = int64_of_sbytes data in
    Array.set m.regs (rind reg) data_int64
  )
  | Ind1 Lbl _ -> raise UnresolvedLabel
  | Ind1 Lit ind_addr -> (
    let start_index = addr_start_index ind_addr in
    let addr_sbytes = read_8_bytes_from_mem m start_index in
    let addr = int64_of_sbytes addr_sbytes in
    let start_index = addr_start_index addr in
    write_8_bytes_to_mem m start_index data
  )
  | Ind2 reg -> (
    let reg_val = reg_val m reg in
    let start_index = addr_start_index reg_val in
    write_8_bytes_to_mem m start_index data
  )
  | Ind3 (Lbl _, reg) -> raise UnresolvedLabel
  | Ind3 (Lit offset, reg) -> (
    let reg_val = reg_val m reg in
    let index = addr_start_index reg_val in
    let start_index = index + Int64.to_int offset in
    write_8_bytes_to_mem m start_index data
  )

let update_flags = fun m res ->
  match (Int64.compare res Int64.zero) with
  | 0 -> (
    m.flags.fz <- true;
    m.flags.fs <- false;
  )
  | -1 -> (
    m.flags.fz <- false;
    m.flags.fs <- true;
  )
  | 1 -> (
    m.flags.fz <- false;
    m.flags.fs <- false;
  )
  | _ -> failwith "unexpected result" 
  

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
exception OperandError

let step (m:mach) : unit =
  let rip = (Array.get  m.regs (rind Rip)) in
  let opt_addr = (map_addr rip) in
  begin match opt_addr with
  | None -> () (* TODO: Check termination condition *)
  | Some(addr) -> (
    let instructionOpt = (Array.get m.mem addr) in
    match instructionOpt with
    | InsFrag -> ()
    | Byte _ -> ()
    | InsB0 (opcode, operands) ->
      match opcode with
      | Negq -> (
        match operands with
        | dest::[] -> (
          let data_sbytes = read m dest in
          let data_int64 = int64_of_sbytes data_sbytes in
          let overflow = Int64.equal (Int64.min_int) data_int64 in
          let complement = Int64.neg data_int64 in
          begin
            match overflow with
            | true ->
               m.flags.fo <- true
            | false ->
               (* TODO: Verify if the correct behaviour of overflow on
                  negation involves not setting negated value. *)
               update_flags m complement;
               let result_sbytes = sbytes_of_int64 complement in
               write m dest result_sbytes
          end
        )
        | _ -> raise OperandError
      )
      | Movq -> (
        match operands with
        | src::dest::[] -> (
          let data = read m src in
          write m dest data
        )
        | _ -> raise OperandError
      )
      | Pushq ->
         begin match operands with
         | src::[] -> (
           m.regs.(rind Rsp) <- Int64.sub (m.regs.(rind Rsp)) 8L;
           let src_data = read m src in
           write m (Ind2 Rsp) src_data;
         )
         | _ -> raise OperandError
         end
      | Popq ->
         begin match operands with
         | dest::[] -> (
           let top_of_stack_data = read m (Ind2 Rsp) in
           write m dest top_of_stack_data;
           m.regs.(rind Rsp) <- Int64.add (m.regs.(rind Rsp)) 8L;
         )
         | _ -> raise OperandError
         end
      | Leaq ->
         begin match operands with
         | ind::dest::[] ->
            begin match ind with
            | Ind1 Lit quad ->
               let addr_sbytes = sbytes_of_int64 quad in
               write m dest addr_sbytes;
            | Ind2 reg ->
               let addr_sbytes = sbytes_of_int64 (reg_val m reg) in
               write m dest addr_sbytes;
            | Ind3 (Lit offset, reg) ->
               let addr_sbytes = sbytes_of_int64 (Int64.add (reg_val m reg) offset) in
               write m dest addr_sbytes;
            | _ -> raise OperandError
            end
         | _ -> raise OperandError
         end
      | Incq ->
         begin match operands with
         | dest::[] -> (
           let d64 = int64_of_sbytes (read m dest) in
           let s64 = 1L in
           let r64 = Int64.add d64 s64 in
           if (d64 < 0L && s64 < 0L && r64 > 0L) || (d64 > 0L && s64 > 0L && r64 < 0L) then
             m.flags.fo <- true
           else
             m.flags.fo <- false;
           write m dest (sbytes_of_int64 r64);
           update_flags m r64;
         )
         | _ -> raise OperandError
         end
      | Decq ->
         begin match operands with
         | dest::[] -> (
           let d64 = int64_of_sbytes (read m dest) in
           let s64 = 1L in
           let r64 = Int64.sub d64 s64 in
           if (s64 = Int64.min_int) || (d64 < 0L && (Int64.sub 0L s64) < 0L && r64 > 0L) || (d64 > 0L && (Int64.sub 0L  s64) > 0L && r64 < 0L) then
             m.flags.fo <- true
           else
             m.flags.fo <- false;
           write m dest (sbytes_of_int64 r64);
           update_flags m r64;
         )
         | _ -> raise OperandError
         end
      | Notq
      | Addq ->
         begin match operands with
         | src::dest::[] -> (
           let d64 = int64_of_sbytes (read m dest) in
           let s64 = int64_of_sbytes (read m src) in
           let r64 = Int64.add d64 s64 in
           if (d64 < 0L && s64 < 0L && r64 > 0L) || (d64 > 0L && s64 > 0L && r64 < 0L) then
             m.flags.fo <- true
           else
             m.flags.fo <- false;
           write m dest (sbytes_of_int64 r64);
           update_flags m r64;
         )
         | _ -> raise OperandError
         end
      | Subq ->
         begin match operands with
         | src::dest::[] -> (
           let d64 = int64_of_sbytes (read m dest) in
           let s64 = int64_of_sbytes (read m src) in
           let r64 = Int64.sub d64 s64 in
           if (s64 = Int64.min_int) || (d64 < 0L && (Int64.sub 0L s64) < 0L && r64 > 0L) || (d64 > 0L && (Int64.sub 0L  s64) > 0L && r64 < 0L) then
             m.flags.fo <- true
           else
             m.flags.fo <- false;
           write m dest (sbytes_of_int64 r64);
           update_flags m r64;
         )
         | _ -> raise OperandError
         end
      | Imulq ->
         begin match operands with
         | src::dest::[] -> (
           let d64 = int64_of_sbytes (read m dest) in
           let s64 = int64_of_sbytes (read m src) in
           let r64 = Int64.mul d64 s64 in (* Note that (-(2^63)) * -1 overflows. *)
           if (s64 = 0L  || d64 = 0L) || ((not (s64 = -1L && d64 = -0x80000000L)) && s64 = (Int64.div r64 d64)) then
             m.flags.fo <- false
           else
             m.flags.fo <- true;
           write m dest (sbytes_of_int64 r64);
         )
         | _ -> raise OperandError
         end
      | Xorq
      | Orq
      | Andq
      | Shlq
      | Sarq
      | Shrq
      | Jmp ->
         begin match operands with
         | src::[] -> (
           let src64 = int64_of_sbytes (read m src) in
           m.regs.(rind Rip) <- Int64.sub src64 8L; (* Compensates for last line of step function. *)
         )
         | _ -> raise OperandError
         end
      | J(cnd) ->
         begin match operands with
         | src::[] ->
            if interp_cnd m.flags cnd then
              let src64 = int64_of_sbytes (read m src) in
              m.regs.(rind Rip) <- Int64.sub src64 8L; (* Compensates for last line of step function. *)
         | _ -> raise OperandError
         end
      | Cmpq ->
         begin match operands with
         | src1::src2::[] -> (
           let d64 = int64_of_sbytes (read m src2) in
           let s64 = int64_of_sbytes (read m src1) in
           let r64 = Int64.sub d64 s64 in
           if (s64 = Int64.min_int) || (d64 < 0L && (Int64.sub 0L s64) < 0L && r64 > 0L) || (d64 > 0L && (Int64.sub 0L  s64) > 0L && r64 < 0L) then
             m.flags.fo <- true
           else
             m.flags.fo <- false;
           (* write m dest (sbytes_of_int64 r64); *)
           update_flags m r64;
         )
         | _ -> raise OperandError
         end
      | Set(_)
      | Callq
      | Retq -> ()
  )
  end;
  m.regs.(rind Rip) <- Int64.add rip (Int64.of_int(8))


(* Runs the machine until the rip register reaches a designated
   memory address. *)
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
