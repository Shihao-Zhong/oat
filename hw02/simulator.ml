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
let interp_cnd {fo; fs; fz} : cnd -> bool =
  function
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
let read_from_addr = fun m addr ->
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

let write_to_addr = fun m addr data ->
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

let update_fs_and_fz_flags = fun m res ->
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

let increment_stack_pointer m =
  m.regs.(rind Rsp) <- Int64.sub (m.regs.(rind Rsp)) 8L

let decrement_stack_pointer m =
  m.regs.(rind Rsp) <- Int64.add (m.regs.(rind Rsp)) 8L

let increment_program_counter m =
  m.regs.(rind Rip) <- Int64.add (m.regs.(rind Rip)) 8L

let perform_arithmetic_instruction = fun m op src dest overflow_cond ->
  let read = read_from_addr m in
  let write = write_to_addr m in
  let update_fs_and_fz_flags = update_fs_and_fz_flags m in
  let d64 = int64_of_sbytes (read dest) in
  let s64 = int64_of_sbytes (read src) in
  let r64 = op d64 s64 in
  begin
    m.flags.fo <- overflow_cond s64 d64 r64;
    write dest (sbytes_of_int64 r64);
    update_fs_and_fz_flags r64;
  end

let perform_logical_instruction = fun m op src dest ->
  let read = read_from_addr m in
  let write = write_to_addr m in
  let update_fs_and_fz_flags = update_fs_and_fz_flags m in
  let src_int64 = int64_of_sbytes (read src) in
  let dest_int64 = int64_of_sbytes (read dest) in
  let result_int64 = op src_int64 dest_int64 in
  begin
    write dest (sbytes_of_int64 result_int64);
    update_fs_and_fz_flags result_int64;
    m.flags.fo <- false;
  end

let perform_shift_instruction = fun m op amt dest overflow_cond ->
  let read = read_from_addr m in
  let write = write_to_addr m in
  let update_fs_and_fz_flags = update_fs_and_fz_flags m in
  let amt_int = Int64.to_int (int64_of_sbytes (read amt)) in
  let dest_int64 = int64_of_sbytes (read dest) in
  let result_int64 = op dest_int64 amt_int in
  begin
    write dest (sbytes_of_int64 result_int64);
    match amt_int with
    | 0 -> ()
    | 1 -> (
        update_fs_and_fz_flags result_int64;
        m.flags.fo <- overflow_cond dest_int64;
      )
    | _ -> update_fs_and_fz_flags result_int64
  end

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
exception OperandError

let step (m:mach) : unit =
  let read = read_from_addr m in
  let write = write_to_addr m in
  let update_fs_and_fz_flags = update_fs_and_fz_flags m in
  let decrement_stack_pointer = fun () -> decrement_stack_pointer m in
  let increment_stack_pointer = fun () -> increment_stack_pointer m in
  let increment_program_counter = fun () -> increment_program_counter m in
  let perform_arithmetic_instruction = perform_arithmetic_instruction m in
  let perform_logical_instruction = perform_logical_instruction m in
  let perform_shift_instruction = perform_shift_instruction m in
  let rip = (Array.get  m.regs (rind Rip)) in
  let opt_addr = (map_addr rip) in
  let fallthrough_predicate = ref false in
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
                  let dest_sbytes = read dest in
                  let dest_int64 = int64_of_sbytes dest_sbytes in
                  let overflow = Int64.equal Int64.min_int dest_int64 in
                  let complement = Int64.neg dest_int64 in
                  begin
                    m.flags.fo <- overflow;
                    update_fs_and_fz_flags complement;
                    let result_sbytes = sbytes_of_int64 complement in
                    write dest result_sbytes;
                  end
                )
              | _ -> raise OperandError
            )
          | Movq -> (
              match operands with
              | src::dest::[] -> (
                  let src_sbytes = read src in
                  write dest src_sbytes
                )
              | _ -> raise OperandError
            )
          | Pushq ->
            begin match operands with
              | src::[] -> (
                  increment_stack_pointer();
                  let src_sbytes = read src in
                  write (Ind2 Rsp) src_sbytes;
                )
              | _ -> raise OperandError
            end
          | Popq ->
            begin match operands with
              | dest::[] -> (
                  let top_of_stack_sbytes = read (Ind2 Rsp) in
                  write dest top_of_stack_sbytes;
                  decrement_stack_pointer();
                )
              | _ -> raise OperandError
            end
          | Leaq -> (
              let (addr_sbytes, dest) = begin match operands with
                | (Ind1 Lit quad)::dest::[] -> (sbytes_of_int64 quad, dest)
                | (Ind2 reg)::dest::[] -> (sbytes_of_int64 (reg_val m reg), dest)
                | (Ind3 (Lit offset, reg))::dest::[] -> (sbytes_of_int64 (Int64.add (reg_val m reg) offset), dest)
                | _ -> raise OperandError
              end
              in
              write dest addr_sbytes
            )
          | Incq ->
            begin match operands with
              | dest::[] ->
                perform_arithmetic_instruction Int64.add (Imm (Lit 1L)) dest (fun s64 d64 r64 -> (d64 < 0L && s64 < 0L && r64 > 0L) || (d64 > 0L && s64 > 0L && r64 < 0L))
              | _ -> raise OperandError
            end
          | Decq ->
            begin match operands with
              | dest::[] -> 
                perform_arithmetic_instruction Int64.sub (Imm (Lit 1L)) dest (fun s64 d64 r64 -> (d64 < 0L && (Int64.sub 0L s64) < 0L && r64 > 0L) || (d64 > 0L && (Int64.sub 0L  s64) > 0L && r64 < 0L))
              | _ -> raise OperandError
            end
          | Addq ->
            begin match operands with
              | src::dest::[] -> 
                perform_arithmetic_instruction Int64.add src dest (fun s64 d64 r64 -> (d64 < 0L && s64 < 0L && r64 > 0L) || (d64 > 0L && s64 > 0L && r64 < 0L))
              | _ -> raise OperandError
            end
          | Subq ->
            begin match operands with
              | src::dest::[] ->
                perform_arithmetic_instruction Int64.sub src dest (fun s64 d64 r64 -> (d64 < 0L && (Int64.sub 0L s64) < 0L && r64 > 0L) || (d64 > 0L && (Int64.sub 0L  s64) > 0L && r64 < 0L))
              | _ -> raise OperandError
            end
          | Imulq ->
            begin match operands with
              | src::dest::[] ->
                perform_arithmetic_instruction Int64.mul src dest (fun s64 d64 r64 -> not ((s64 = 0L  || d64 = 0L) || ((not (s64 = -1L && d64 = -0x80000000L)) && s64 = (Int64.div r64 d64))))
              | _ -> raise OperandError
            end
          | Jmp ->
            begin match operands with
              | src::[] -> (
                  let src_int64 = int64_of_sbytes (read src) in
                  m.regs.(rind Rip) <- src_int64;
                  fallthrough_predicate := true;
                )
              | _ -> raise OperandError
            end
          | J(cnd) ->
            begin match operands with
              | src::[] ->
                if interp_cnd m.flags cnd then
                  let src_int64 = int64_of_sbytes (read src) in
                  m.regs.(rind Rip) <- src_int64;
                  fallthrough_predicate := true;
              | _ -> raise OperandError
            end
          | Cmpq ->
            begin match operands with
              | src1::src2::[] -> (
                  let d64 = int64_of_sbytes (read src2) in
                  let s64 = int64_of_sbytes (read src1) in
                  let r64 = Int64.sub d64 s64 in
                  if (s64 = Int64.min_int) || (d64 < 0L && (Int64.sub 0L s64) < 0L && r64 > 0L) || (d64 > 0L && (Int64.sub 0L  s64) > 0L && r64 < 0L) then
                    m.flags.fo <- true
                  else
                    m.flags.fo <- false;
                  (* write dest (sbytes_of_int64 r64); *)
                  update_fs_and_fz_flags r64;
                )
              | _ -> raise OperandError
            end
          | Callq ->
            begin match operands with
              | src::[] -> (
                  increment_stack_pointer();
                  let rip_sbytes = read (Reg Rip) in
                  write (Ind2 Rsp) rip_sbytes;
                  let src_int64 = int64_of_sbytes (read src) in
                  m.regs.(rind Rip) <- src_int64;
                  fallthrough_predicate := true;
                )
              | _ -> raise OperandError
            end 
          | Retq ->
            begin match operands with
              | [] ->
                begin
                  let top_of_stack_sbytes = read (Ind2 Rsp) in
                  let top_of_stack_int64 = int64_of_sbytes top_of_stack_sbytes in
                  m.regs.(rind Rip) <- top_of_stack_int64;
                  if m.regs.(rind Rip) = exit_addr then
                    fallthrough_predicate := true (* exit_addr is at mem_top so decrement_stack_pointer
                                                     call would result in an out of bounds exception when
                                                     executing `read (Ind2 Rsp)` *)
                  else
                    decrement_stack_pointer();
                end
              | _ -> raise OperandError
            end
          | Notq ->
            begin match operands with
              | dest::[] ->
                let dest_int64 = int64_of_sbytes (read dest) in
                let result_int64 = Int64.lognot dest_int64 in
                begin
                  write dest (sbytes_of_int64 result_int64);
                  update_fs_and_fz_flags result_int64;
                end
              | _ -> raise OperandError
            end
          | Xorq ->
            begin match operands with
              | src::dest::[] -> perform_logical_instruction Int64.logxor src dest
              | _ -> raise OperandError
            end
          | Orq ->
            begin match operands with
              | src::dest::[] -> perform_logical_instruction Int64.logor src dest
              | _ -> raise OperandError
            end
          | Andq ->
            begin match operands with
              | src::dest::[] -> perform_logical_instruction Int64.logand src dest
              | _ -> raise OperandError
            end
          | Shlq ->
            begin match operands with
              | amt::dest::[] ->
                perform_shift_instruction Int64.shift_left amt dest (fun dest_int64 -> (
                      let sign_bit = Int64.shift_right_logical dest_int64 63 |> Int64.to_int in
                      let most_sig_bit = Int64.shift_right_logical dest_int64 62 |> Int64.logand 1L |> Int64.to_int in
                      sign_bit <> most_sig_bit
                    ))
              | _ -> raise OperandError
            end
          | Sarq ->
            begin match operands with
              | amt::dest::[] ->
                perform_shift_instruction Int64.shift_right amt dest (fun _dest_int64 -> false)
              | _ -> raise OperandError
            end
          | Shrq ->
            begin match operands with
              | amt::dest::[] ->
                perform_shift_instruction Int64.shift_right_logical amt dest (fun dest_int64 -> (
                      let sign_bit = Int64.shift_right_logical dest_int64 63 |> Int64.to_int in
                      sign_bit = 1
                    ))
              | _ -> raise OperandError
            end
          | Set(cnd) -> 
            begin match operands with
              | dest::[] ->
                let dest_sbytes = sbytes_of_int64 (int64_of_sbytes (read dest)) in
                let result_sbytes = match (dest_sbytes, (interp_cnd m.flags cnd)) with
                  | (hd::tail, true) -> Byte(Char.chr 1)::tail
                  | (hd::tail, false) -> Byte(Char.chr 0)::tail
                  | _ -> failwith "Invalid State"
                in
                write dest result_sbytes
              | _ -> raise OperandError
            end
      )
  end;
  if not !fallthrough_predicate then
    increment_program_counter()


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

(* Ensure all the labels are unique *)
module SS = Set.Make(String)

let assert_labels_are_unique p =
  let rec aux = fun p label_set ->
    match p with
    | hd::tail when SS.mem hd.lbl label_set -> raise (Redefined_sym hd.lbl)
    | hd::tail -> aux tail (SS.add hd.lbl label_set)
    | _ -> () 
  in
  aux p SS.empty

(* Calculate the size of each construct in number of sybtes required to represent it *)
let quad_size = 8

let data_size =
  function
  | Asciz(s) -> (String.length s) + 1
  | Quad(_) -> quad_size

let instruction_size = 8

let asm_size =
  function
  | Text(instructions) -> (List.length instructions) * instruction_size
  | Data(data_list) -> List.fold_left (fun curr_size data -> curr_size + (data_size data)) 0 data_list

let elem_size elm = asm_size elm.asm

let program_size p =
  List.fold_left (fun curr_size elm -> curr_size + (elem_size elm)) 0 p

(* Generate a label index map *)
let generate_label_index_map = fun p start_index ->
  let (+) = Int64.add in
  let aux = fun (map, curr_index) elm ->
    let map = (elm.lbl, curr_index)::map in
    let curr_index = curr_index + (Int64.of_int (elem_size elm)) in
    (map, curr_index)
  in
  let (label_index_map, _) = List.fold_left aux ([], start_index) p in
  label_index_map

(* split text and data of a program *)
let split_text_and_data p =
  let rec aux = fun p text data ->
    match p with
    | hd::tail -> (
        match hd.asm with
        | Text(_) -> aux tail (hd::text) data
        | Data(_) -> aux tail text (hd::data)
      )
    | [] -> (List.rev text, List.rev data)
  in
  aux p [] []

(* Entry point *)
let label_index = fun label_index_map label ->
  let rec aux =
    function
    | (key, index)::_ when key = label -> index
    | _::tail -> aux tail
    | [] -> raise (Undefined_sym label)
  in aux label_index_map

let entry_address label_index_map = label_index label_index_map "main"

(* Resolve labels *)
let resolve_labels_in_operands = fun label_index_map operands ->
  let label_index = label_index label_index_map in
  let resolve_opreand_label =
    function
    | Imm(Lbl(lbl)) -> Imm(Lit(label_index lbl))
    | Ind1(Lbl(lbl)) -> Ind1(Lit(label_index lbl))
    | Ind3(Lbl(lbl), reg) -> Ind3(Lit(label_index lbl), reg)
    | operand -> operand
  in
  List.map resolve_opreand_label operands 

let resolve_labels_in_instructions = fun label_index_map instructions ->
  let resolve_labels = resolve_labels_in_operands label_index_map in
  List.map (fun (opcode, operands) -> (opcode, resolve_labels operands)) instructions

let resolve_labels_in_data = fun label_index_map data_list ->
  let aux =
    function
    | Quad(Lbl(lbl)) -> Quad(Lit(label_index label_index_map lbl))
    | data -> data
  in
  List.map aux data_list

let resolve_labels_in_program = fun label_index_map p ->
  let resolve_labels_in_instructions = resolve_labels_in_instructions label_index_map in
  let resolve_labels_in_data = resolve_labels_in_data label_index_map in
  let aux = fun element ->
    match element.asm with
    | Text(instructions) -> { element with asm = Text(resolve_labels_in_instructions instructions) }
    | Data(data) -> { element with asm = Data(resolve_labels_in_data data) }
  in
  List.map aux p

let sbytes_of_program = fun p ->
  let aux =
    function
    | Text(instructions) -> List.flatten (List.map sbytes_of_ins instructions)
    | Data(data) -> List.flatten (List.map sbytes_of_data data)
  in
  let asms = List.map (fun e -> e.asm) p in
  List.flatten (List.map aux asms)

(* print for debugging *)
let string_of_ins_sbytes = fun sbytes ->
  let predicate =
    function
    | InsB0(ins) -> true
    | _ -> false
  in 
  let sbyte_to_string =
    function
    | InsB0(ins) -> string_of_ins ins
    | _ -> ""
  in
  let ins_strings = (List.filter predicate sbytes) |> (List.map sbyte_to_string) in
  List.iter (fun s -> print_endline s) ins_strings

let assemble (p:prog) : exec =
  let () = assert_labels_are_unique p in
  let (text_seg, data_seg) = split_text_and_data p in
  let text_pos = mem_bot in
  let text_seg_size = program_size text_seg in
  let data_pos = Int64.add mem_bot (Int64.of_int text_seg_size) in
  let text_label_index_map = generate_label_index_map text_seg text_pos in
  let data_label_index_map = generate_label_index_map data_seg data_pos in
  let label_index_map = text_label_index_map @ data_label_index_map in
  let resolved_text_segment = resolve_labels_in_program label_index_map text_seg in
  let resolved_data_segment = resolve_labels_in_program label_index_map data_seg in
  let entry = entry_address text_label_index_map in
  let text_sbytes = sbytes_of_program resolved_text_segment in
  let data_sbytes = sbytes_of_program resolved_data_segment in
  {
    entry = entry
  ; text_pos = text_pos
  ; data_pos = data_pos
  ; text_seg = text_sbytes
  ; data_seg = data_sbytes
  }

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
let init_mem {entry; text_pos; data_pos; text_seg; data_seg} : mem =
  let mem = Array.make mem_size (Byte (Char.chr 0)) in
  let text_pos = Int64.to_int text_pos in
  let data_pos = Int64.to_int data_pos in
  begin
    List.iteri (fun index sbyte -> Array.set mem (index + text_pos - (Int64.to_int mem_bot)) sbyte) text_seg;
    List.iteri (fun index sbyte -> Array.set mem (index + data_pos - (Int64.to_int mem_bot)) sbyte) data_seg;
    List.iteri (fun ind sb -> Array.set mem ((Int64.to_int (Int64.sub (Int64.sub mem_top 8L) mem_bot)) + ind) sb) (sbytes_of_int64 exit_addr);
    mem
  end


let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let mem = init_mem {entry; text_pos; data_pos; text_seg; data_seg} in
  let flags = {
    fo = false; fs = false; fz = false;
  } in
  let regs = Array.make 17 Int64.zero in
  begin
    Array.set regs (rind Rip) entry;
    Array.set regs (rind Rsp) (Int64.sub mem_top 8L);
    {
      mem = mem;
      flags = flags;
      regs = regs;
    }
  end
