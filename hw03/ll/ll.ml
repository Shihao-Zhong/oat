(* LLVMlite: A simplified subset of LLVM IR *)

(* Local identifiers *)
type uid = string

(* Global identifiers *)
type gid = string

(* Named types *)
type tid = string

(* Labels *)
type lbl = string

(* LLVM types *)
type ty =
  | Void
  | I1
  | I8
  | I64
  | Ptr of ty
  | Struct of ty list (* field types *)
  | Array of int * ty (* length | type of elements *)
  | Fun of ty list * ty (* return type | argument types *)
  | Namedt of tid (* named type *)

(* Function type: argument types and return type *)
type fty = ty list * ty

(* Syntactic Values *)
type operand =
  | Null
  | Const of int64
  | Gid of gid
  | Id of uid

(* Binary i64 Operations *)
type bop =
  | Add
  | Sub
  | Mul
  | Shl
  | Lshr
  | Ashr
  | And
  | Or
  | Xor

(* Comparison Operators *)
type cnd =
  | Eq
  | Ne
  | Slt
  | Sle
  | Sgt
  | Sge

(* Instructions *)
type insn =
  | Binop of bop * ty * operand * operand (* i64 x i64 -> i64 *)
  | Alloca of ty (* - -> S* *)
  | Load of ty * operand (* S* -> S *)
  | Store of ty * operand * operand (* S x S* -> void *)
  | Icmp of cnd * ty * operand * operand (* S x S -> i1 *)
  | Call of ty * operand * (ty * operand) list (* S1(S2, ..., SN)* x S2 x ... x SN -> S1 *)
  | Bitcast of ty * operand * ty (* T1* -> T2* *)
  | Gep of ty * operand * operand list (* T1* x i64 x ... x i64 -> GEPTY(T1, OP1, ..., OPN)* *)

type terminator =
  | Ret of ty * operand option
  | Br of lbl
  | Cbr of operand * lbl * lbl

(* Basic Blocks *)
type block = { insns : (uid * insn) list; term : (uid * terminator) }

(* Control Flow Graphs: entry and labeled blocks *)
type cfg = block * (lbl * block) list

(* Function Declarations *)
type fdecl = { f_ty : fty; f_param : uid list; f_cfg : cfg }

(* Global Data Initializers *)
type ginit =
  | GNull
  | GGid of gid
  | GInt of int64
  | GString of string
  | GArray of (ty * ginit) list
  | GStruct of (ty * ginit) list

(* Global Declarations *)
type gdecl = ty * ginit

(* LLVMlite Programs *)
type prog = {
  tdecls : (tid * ty) list;
  gdecls : (gid * gdecl) list;
  fdecls : (gid * fdecl) list;
  edecls : (gid * ty) list
}
