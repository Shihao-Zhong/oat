(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understinging this entire file and 
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

let compile_biop = function
  | Add -> Addq | Sub -> Subq | Mul -> Imulq
  | Shl -> Shlq | Lshr -> Shrq | Ashr -> Sarq
  | And -> Andq | Or -> Orq | Xor -> Xorq 

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

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from ebp (in bytes) that represents a storage slot in
   the stack.  
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* other helper function *)
let wordSize = 8
type offset = int
let fromRbp = fun i -> Ind3(Lit(Int64.of_int i), Rbp)
let pushRegIntoStack reg = Pushq, [Reg(reg)]

let calleeSaveReg = [Rbx; R12; R13; R14; R15]
let callerSaveReg = [Rax; Rcx; Rdx; Rsi; Rdi; Rsp; R08; R09; R10; R11]

let numArgsStoredInReg = 6
let argRegMap = function
  | 0 -> Reg Rdi
  | 1 -> Reg Rsi
  | 2 -> Reg Rdx
  | 3 -> Reg Rcx
  | 4 -> Reg R08
  | 5 -> Reg R09
  | _ -> failwith "only for the first six args"

let rec first n l =
  match (n, l) with
  | (0, l) -> []
  | (_, []) -> []
  | (n, hd::tail) -> hd::(first (n - 1) tail)

let rec after n l =
  match (n, l) with
  | (0, l) -> l
  | (_, []) -> []
  | (n, hd::tail) -> after (n - 1) tail

let splitAfter n l = (first n l, after n l)


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
let compile_operand (ctxt : ctxt) (dest : X86.operand) : Ll.operand -> ins =
  let { layout } = ctxt in
  fun op -> match op with
    | Null -> (Movq, [Imm(Lit(Int64.zero)); dest])
    | Const(c) -> (Movq, [Imm(Lit(c)); dest])
    | Id(uid) -> 
      let src = lookup layout uid in
      (Movq, [src; dest])
    | Gid(gid) -> 
      let mangled = Platform.mangle(gid) in
      (Leaq, [Ind3(Lbl(mangled), Rip); dest])

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
let compile_call ctxt uid fn args = 
  let compile_operand = compile_operand ctxt in
  let args = args |> List.map (fun (_, src) -> src) in
  let pushCallerSaveRegIns = callerSaveReg |> List.map pushRegIntoStack in
  let copyFirstSixArgsIns =
    args
    |> first numArgsStoredInReg
    |> List.mapi (fun i src -> compile_operand (argRegMap i) src)
  in
  let pushRemainingArgsInRevIns = 
    args
    |> after numArgsStoredInReg
    |> List.rev
    |> List.map (fun  src -> [compile_operand (Reg Rax) src; (Pushq, [(Reg Rax)])])
    |> List.flatten
  in
  let invoke = (
    let pushFnAddrToRax = compile_operand (Reg Rax) fn in
    let callFnPointedToByRax = Callq, [Reg Rax] in
    let storeTheReturnValue = Movq, [(Reg Rax); lookup ctxt.layout uid] in
    [pushFnAddrToRax; callFnPointedToByRax; storeTheReturnValue]
  )
  in
  let removeArgsFromStack =
    let numArgsInStack = args |> after numArgsStoredInReg |> List.length in
    let offset = wordSize * numArgsInStack in
    [(Addq, [Imm(Lit(Int64.of_int(offset))); (Reg Rsp)])]
  in
  let restoreCallerSaveRegIns = callerSaveReg |> List.rev |> List.map (fun reg -> (Popq, [(Reg reg)])) in
  pushCallerSaveRegIns @ copyFirstSixArgsIns @ pushRemainingArgsInRevIns @ invoke @ removeArgsFromStack @ restoreCallerSaveRegIns

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelmentptr, you must generate x86 code that performs
   the appropriate arithemetic calculations.
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
let rec size_ty (tdecls : (tid * ty) list) t : int =
  match t with
  | Void | I8 | Fun _ -> 0 
  | I1 | I64 | Ptr _ -> wordSize
  | Struct tys -> tys |> List.fold_left (fun acc ty -> acc + (size_ty tdecls ty)) 0
  | Array(len, ty) -> len * (size_ty tdecls ty)
  | Namedt(tid) -> size_ty tdecls (lookup tdecls tid)

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

let offset_into_array_ins index finalPointer tdecls ty = 
  let size = size_ty tdecls ty in
  let moveIndToRax = (Movq, [index; (Reg Rax)]) in
  let calcOffsetIns = (Imulq, [Imm(Lit(Int64.of_int(size))); (Reg Rax)]) in
  let calcNewPointerIns = (Addq, [Reg Rax; finalPointer]) in
  [moveIndToRax; calcOffsetIns; calcNewPointerIns]

let offset_into_struct_ins index finalPointer tdecls (types: ty list) = 
  let priorTypes = first index types in
  let offset = priorTypes |> List.fold_left (fun acc ty -> acc + (size_ty tdecls ty)) 0 in 
  let calcNewPointerIns = (Addq, [Imm(Lit(Int64.of_int(offset))); finalPointer]) in
  [calcNewPointerIns]

let compile_gep (ctxt : ctxt) ((ty, op) : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  (* definitions *)
  let finalPtrOp = Reg R08 in
  let indexOp = Reg R09 in
  (* curry helper functions *)
  let compile_operand = compile_operand ctxt in
  let offset_into_array_ins = offset_into_array_ins indexOp finalPtrOp ctxt.tdecls in
  (* Check types *)
  let (firstInd, rest) = match path with
    | hd::tail -> (hd, tail)
    | [] -> failwith "GEP path should not be empty"
  in 
  let ty = match ty with
    | Ptr(ty) -> ty
    | _ -> failwith "GEP should be called with a Ptr type"
  in
  (* First offset instructions *)
  let storeFirstIndIns = compile_operand indexOp firstInd in
  let storeFinalPtrIns = compile_operand finalPtrOp op in
  let addFirstOffsetToPtr = offset_into_array_ins ty in
  [storeFirstIndIns; storeFinalPtrIns] @ addFirstOffsetToPtr


(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Set instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt : ctxt) ((uid : uid), (i : insn)) : X86.ins list =
  let {tdecls; layout} = ctxt in
  let compile_operand = compile_operand ctxt in
  match i with
  | Binop(biop, ty, op1, dest) ->
    let loadOp1Ins = compile_operand (Reg Rax) op1 in
    let loadDestIns = compile_operand (Reg Rcx) dest in
    let exectBopIns = (compile_biop biop, [(Reg Rcx); (Reg Rax)]) in
    let saveResToUidIns = (Movq, [(Reg Rax); (lookup layout uid)]) in
    [loadOp1Ins; loadDestIns; exectBopIns; saveResToUidIns]
  | Icmp(cnd, ty, op1, op2) ->
    let cndX86 = compile_cnd cnd in
    let loadOp1Ins = compile_operand (Reg Rax) op1 in
    let loadOp2Ins = compile_operand (Reg Rcx) op2 in
    let execCmpIns = (Cmpq, [(Reg Rcx); (Reg Rax)]) in
    let storeResIns = (Set cndX86,  [lookup layout uid]) in
    loadOp1Ins::loadOp2Ins::execCmpIns::storeResIns::[]
  | Alloca(ty) ->
    let allocWordIns = (Addq, [Imm(Lit(Int64.of_int(-wordSize))); Reg(Rsp)]) in
    let storeResIns = (Movq, [Reg(Rsp); (lookup layout uid)]) in
    [allocWordIns; storeResIns]
  | Load(ty, p) ->
    let moveToRegIns = compile_operand (Reg Rax) p in
    let interStoreIns = (Movq, [Ind2(Rax); (Reg R08)]) in
    let copyFromRegToDestIns = (Movq, [(Reg R08); (lookup layout uid)]) in
    [moveToRegIns; interStoreIns; copyFromRegToDestIns]
  | Store(ty, op1, op2) -> 
    let loadOp1Ins = compile_operand (Reg Rax) op1 in
    let loadOp2Ins = compile_operand (Reg R08) op2 in
    let storeOp1InOp2Ins = (Movq, [Reg(Rax); Ind2(R08)]) in
    [loadOp1Ins; loadOp2Ins; storeOp1InOp2Ins]
  | Bitcast(t1, op, t2) ->
    let loadOpIns = compile_operand (Reg Rax) op in
    let storeToUid = (Movq, [(Reg Rax); (lookup layout uid)]) in
    [loadOpIns; storeToUid]
  | Call(ty, fn, args) -> compile_call ctxt uid fn args
  | Gep(ty, op, path) -> compile_gep ctxt (ty, op) path

(* compiling terminators  --------------------------------------------------- *)

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional
*)

let restoreCalleeSaveRegIns = calleeSaveReg |> List.mapi (fun ind reg -> (Movq, [fromRbp (-wordSize * (ind + 1)); Reg(reg)]))
let clearStackIns = [(Movq, [Reg(Rbp); Reg(Rsp)])]
let restoreCallerStackBasePointerIns = [(Popq, [Reg(Rbp)])]
let exitCalleeIns = restoreCalleeSaveRegIns @ clearStackIns @ restoreCallerStackBasePointerIns @ [(Retq, [])]

let compile_terminator (ctxt : ctxt) (t : terminator) : X86.ins list =
  match t with
  | Ret(_, None) -> exitCalleeIns
  | Ret(_, Some(Id(uid))) -> (Movq, [lookup ctxt.layout uid; Reg(Rax)])::exitCalleeIns
  | Ret(_, Some(Const(c))) -> (Movq, [Imm(Lit(c)); Reg(Rax)])::exitCalleeIns
  | Br(lbl) -> [(Jmp, [Imm(Lbl(lbl))])]
  | Cbr(cndOp, lbl1, lbl2) -> 
    let compileCndIns = compile_operand ctxt (Reg Rax) cndOp in
    let checkCndOpIns = (Cmpq, [Imm(Lit(1L)); Reg(Rax)]) in
    let handleTrueIns = (J Eq, [Imm(Lbl(lbl1))]) in 
    let handleFalseIns = (Jmp, [Imm(Lbl(lbl2))]) in
    [compileCndIns; checkCndOpIns; handleTrueIns; handleFalseIns]
  | _ -> failwith "kill both of us"

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. *)
let compile_block (ctxt : ctxt) (blk : block) : ins list =
  let compile_insn = compile_insn ctxt in
  let compile_terminator = compile_terminator ctxt in
  let {insns; term=(_, t)} = blk in
  let compiledInstructions = insns |> (List.map compile_insn) |> List.flatten in 
  let compiledTerminator = compile_terminator t in
  compiledInstructions @ compiledTerminator

let compile_lbl_block lbl (ctxt : ctxt) (blk : block) : elem =
  Asm.text lbl (compile_block ctxt blk)

(* compile_fdecl ------------------------------------------------------------ *)

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  if n < numArgsStoredInReg
  then argRegMap n
  (* + 2 accounts for the instruction pointer and base pointer stored on the stack *)
  else fromRbp((n - numArgsStoredInReg + 2) * wordSize)

(* We suggest that you create a helper function that computes the 
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id 
     is also stored as a stack slot.
   - see the discusion about locals 
*)
let blockLayout ({insns; term=(uid, _)}: block) (offset: offset): (layout * offset) =
  let insnsLayout = insns |> List.mapi (fun ind (uid, _) -> (uid, fromRbp(-wordSize * ind + offset))) in
  let offset = offset + (-wordSize * List.length(insns)) in
  let termLayout = (uid, fromRbp(offset)) in
  (termLayout::insnsLayout, offset - wordSize)

let stack_layout (args: uid list) ((block, lbled_blocks): cfg) : layout =
  let offset = -wordSize * (List.length(calleeSaveReg) + 1) in 
  let argsLayout = args |> List.mapi (fun ind uid -> (uid, fromRbp(-wordSize * ind + offset))) in
  let offset = offset + (-wordSize * List.length(args)) in
  let (entryBlockLayout, offset) = (blockLayout block offset) in
  let (lbledBlocksLayout, _) = 
    List.fold_left (
      fun (layoutStream, offset) (_, block) ->
        let (layout, offset) = (blockLayout block offset) in
        (layout @ layoutStream, offset)
    ) ([], offset) lbled_blocks
  in
  argsLayout @ entryBlockLayout @ lbledBlocksLayout

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

   -------------------------------------------------------------------
   Personal Notes:

   The invariant when control is transfered to the Callee:
   - Rsp points to the top of the caller stack frame which holds the Rip before the call
   - Rbp is the base pointer of the caller stack frame
   - Rip points to the first instruction of the Callee

   In Callee:
   - Push the base pointer into the stack
   - Update the base pointer to point to the stack pointer and so create a new stack frame
   - Push all the Callee save registers into the stack
   - << CFG >>
   - Restore all the Callee save registers
   - Clean the Callee stack frame
   - Restore the base pointer of the Caller stack frame
   - Return control to Caller
*)
let copyParamsIns (stackLayout: layout) (f_param: uid list): ins list =
  let aux = fun ind uid -> 
    let fromOp = arg_loc ind in 
    let toOp = lookup stackLayout uid in
    (Movq, [fromOp; toOp])
  in
  List.mapi aux f_param

let compile_fdecl (tdecls : (tid * ty) list) (name : gid) { f_ty; f_param; f_cfg } : X86.prog =
  let (entryBlock, lbledBlocks) = f_cfg in
  let layout = stack_layout f_param f_cfg in
  let context: ctxt = {tdecls; layout} in
  let stackPointerOffset = -wordSize * List.length layout in
  (* entry block *)
  let pushBasePointer = pushRegIntoStack Rbp in
  let newStackFrame = Movq, [Reg(Rsp); Reg(Rbp)] in
  let pushCalleeSaveReg = calleeSaveReg |> List.map pushRegIntoStack in
  let newStackPointerIns = (Addq, [Imm(Lit(Int64.of_int(stackPointerOffset))); Reg(Rsp)]) in
  let copyParamIntoStack = copyParamsIns layout f_param in
  let entryPointIns = pushBasePointer::newStackFrame::pushCalleeSaveReg @  newStackPointerIns::copyParamIntoStack in
  let entryBlockIns = compile_block context entryBlock in
  let startElm = {
    lbl= Platform.mangle name;
    global=true;
    asm=Text(entryPointIns @ entryBlockIns)
  } in
  (* labeled blocks *)
  let lbledBlocksElm = lbledBlocks |> List.map (fun (lbl, blk) -> compile_lbl_block lbl context blk) in
  startElm::lbledBlocksElm

(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten

and compile_gdecl (_, g) = compile_ginit g

(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
