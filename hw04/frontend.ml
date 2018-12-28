open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
  let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
         match e with
         | L l ->
           begin match term_opt with
             | None -> 
               if (List.length insns) = 0 then (gs, einsns, [], None, blks)
               else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                                no terminator" l
             | Some term ->
               (gs, einsns, [], None, (l, {insns; term})::blks)
           end
         | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
         | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
         | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
         | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
  in
  match term_opt with
  | None -> failwith "build_cfg: entry block has no terminator" 
  | Some term -> 
    let insns = einsns @ insns in
    ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None

end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the the corresponding integer types. OAT strings are 
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
    let args, ret = cmp_fty (ts, t) in
    Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)


(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate an array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]




(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to bitcast the 
     resulting gid to (Ptr I8)

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

   - we found it useful to write a helper function 
     cmp_exp_as : Ctxt.t -> Ast.exp node -> Ll.ty -> Ll.operand * stream
     that compiles an expression and optionally inserts a bitcast to the
     desired Ll type. This is useful for dealing with OAT identifiers that
     correspond to gids that don't quite have the type you want

*)

let int_comp_cnd : Ast.binop -> Ll.cnd option = function
  | Eq -> Some(Eq)
  | Neq -> Some(Ne)
  | Lt -> Some(Slt)
  | Lte -> Some(Sle)
  | Gt -> Some(Sgt)
  | Gte -> Some(Sge)
  | _ -> None

let ll_bop : Ast.binop -> Ll.bop = function
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | And -> And
  | Or -> Or
  | Shl -> Shl
  | Shr -> Lshr
  | Sar -> Ashr
  | _ -> failwith "unexpected binary operator"

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CInt i -> I64, Const(i), []
  | CBool b -> I1, Const(if b then Int64.one else Int64.zero), []
  | Bop (binop, exp1, exp2) ->
    let (e1_ty, e1_op, e1_stream) = cmp_exp c exp1 in
    let (e2_ty, e2_op, e2_stream) = cmp_exp c exp2 in
    let (_, _, ret_ty) = typ_of_binop binop in
    let ret_ty = cmp_ty ret_ty in
    let uid = gensym "" in (
      match (int_comp_cnd binop) with
      | Some(cnd) ->
        let insn = Icmp(cnd, e1_ty, e1_op, e2_op) in
        (ret_ty, Id(uid), e2_stream >@ e1_stream >:: I(uid, insn))
      | None -> 
        let bop = ll_bop binop in
        let insn = Binop(bop, e1_ty, e1_op, e2_op) in
        (ret_ty, Id(uid), e2_stream >@ e1_stream >:: I(uid, insn))    
    )
  | Id(id) -> (
      let (ty, op) = Ctxt.lookup id c in
      let uid = gensym "" in
      match ty with
      | Ptr(Array(s, ty)) -> Ptr(ty), Id(uid), [I(uid, Bitcast(Ptr(Array(s, ty)), op,  Ptr(ty)))]
      | Ptr(ty) -> ty, Id(uid), [I(uid, Load(Ptr(ty), op))]
      | _ -> failwith "Id expects a Ptr"
    )
  | Uop(op, exp) -> (
      match op with
      | Neg ->
        let minus_one_node = no_loc @@ CInt(Int64.of_int (-1)) in
        let binop_node = no_loc @@ Bop(Mul, exp, minus_one_node) in
        cmp_exp c binop_node
      | Lognot ->
        let flase_node = no_loc @@ CBool(false) in
        let binop_node = no_loc @@ Bop(And, exp, flase_node) in
        cmp_exp c binop_node
      | Bitnot ->
        let minus_one_node = no_loc @@ CInt(Int64.of_int (-1)) in
        let mult_node = no_loc @@ Bop(Mul, exp, minus_one_node) in
        let sub_node = no_loc @@ Bop(Add, mult_node, minus_one_node) in
        cmp_exp c sub_node
    )
  | Call({elt=Id(id)}, args) -> (
      let ptr_fn_ty, op = Ctxt.lookup id c in
      match ptr_fn_ty with
      | Ptr Fun(_, ret_ty) -> 
        let args, stream = List.fold_left (
            fun (ll_args, code) ast_arg ->
              let ty, op, stream = cmp_exp c ast_arg in
              ll_args @ [(ty, op)], code >@ stream
          ) ([], []) args in
        let uid = gensym "" in
        let call: Ll.insn = Call(ret_ty, op, args) in
        ret_ty, Id(uid), stream >:: I(uid, call)
      | _ -> failwith "unexpected type for call"
    )
  | NewArr(ty, exp) -> (
      let _, len_op, len_stream = cmp_exp c exp in
      let arr_ty, arr_op, alloc_arr_stream = oat_alloc_array ty len_op in
      arr_ty, arr_op, len_stream >@ alloc_arr_stream
    )
  | Index(arr_exp, ind_exp) -> (
      let arr_ty, arr_op, arr_stream = cmp_exp c arr_exp in
      let _, ind_op, ind_stream = cmp_exp c ind_exp in
      match arr_ty with
      | Ptr(Struct [_; Array(_, ty)]) ->
        let ptr_uid = gensym "" in
        let value_uid = gensym "" in
        let index_ins = Gep(arr_ty, arr_op, [Const(Int64.zero); Const(Int64.one); ind_op]) in
        let load_ins = Load(Ptr(ty), Id ptr_uid) in
        ty, Id(value_uid), arr_stream >@ ind_stream >:: I(ptr_uid, index_ins) >:: I(value_uid, load_ins)
      | _ -> failwith "unexpected array type"
    )
  | _ -> failwith "cmp_exp unimplemented"


(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations

   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

*)
let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Ret None -> c, [T(Ret(Void, None))]
  | Ret Some(e) -> 
    let (ty, op, stream) = cmp_exp c e in
    c, stream >:: T(Ret(ty, Some op))
  | Decl(id, e) ->
    let uid = gensym "" in
    let (ty, op, stream) = cmp_exp c e in
    let allocate = E(uid, Alloca ty) in
    let store = I("", Store(ty, op, Id uid)) in
    let c = Ctxt.add c id (Ptr ty, Id uid) in
    c, stream >:: allocate >:: store
  | While(cnd, stmts) ->
    let (cnd_ty, cnd_op, cnd_stream) = cmp_exp c cnd in
    let c, body = cmp_stmts c rt stmts in
    let start_lbl = gensym "start" in
    let body_lbl = gensym "body" in
    let else_lbl = gensym "else" in
    let jmp_to_start = T(Br start_lbl) in
    let jmp_while = T(Cbr (cnd_op, body_lbl, else_lbl)) in
    let start_stream = [L(start_lbl)] >@ cnd_stream >:: jmp_while  in
    let body_stream = [L(body_lbl)] >@ body >:: jmp_to_start in
    c, [jmp_to_start] >@ start_stream >@ body_stream >:: L(else_lbl)
  | For(vdecls, cnd, update_count_stmt, stmts) ->
    let c, vdecls_stream = List.fold_left(fun (c, stream_acc) vdecl ->
        let (c, stream) = cmp_stmt c rt (no_loc (Decl vdecl)) in
        c, stream_acc >@ stream
      ) (c, []) vdecls in
    let cnd = match cnd with
      | Some(exp) -> exp
      | None -> no_loc (CBool true)
    in
    let update_count_stmt = match update_count_stmt with 
      | Some(stmt) -> [stmt]
      | None -> []
    in
    let while_stmt = While(cnd, (stmts @ update_count_stmt)) in
    let c, body_stream = cmp_stmt c rt {elt = while_stmt; loc = stmt.loc}in
    c, vdecls_stream >@ body_stream
  | Assn(l, r) -> (
      let (r_ty, r_op, r_stream) = cmp_exp c r in
      match l.elt with
      | Id(id) -> 
        let _, dest_op = Ctxt.lookup id c in
        c, r_stream >:: I("", Store(r_ty, r_op, dest_op))
      | Index(arr_exp, ind_exp) -> (
          let arr_ty, arr_op, arr_stream = cmp_exp c arr_exp in
          let _, ind_op, ind_stream = cmp_exp c ind_exp in
          match arr_ty with
          | Ptr(Struct [_; Array(_, ty)]) ->
            let ptr_uid = gensym "" in
            let index_ins = Gep(arr_ty, arr_op, [Const(Int64.zero); Const(Int64.one); ind_op]) in
            c, arr_stream >@ ind_stream >:: I(ptr_uid, index_ins)
          | _ -> failwith "expected a Ptr to an Array"
        )
      | _ -> failwith "unexpected type"
    )
  | If(cnd, t, e) ->
    let (cnd_ty, cnd_op, cnd_stream) = cmp_exp c cnd in
    let c, t_stream = cmp_stmts c rt t in
    let c, e_stream = cmp_stmts c rt e in
    let start_lbl = gensym "start" in
    let then_lbl = gensym "then" in
    let else_lbl = gensym "else" in
    let post_lbl = gensym "post" in
    let jmp_to_start = T(Br start_lbl) in
    let jmp_to_post = T(Br post_lbl) in
    let jmp_if = T(Cbr (cnd_op, then_lbl, else_lbl)) in
    let start_stream = [L(start_lbl)] >@ cnd_stream >:: jmp_if in
    let then_stream = [L(then_lbl)] >@ t_stream >:: jmp_to_post in
    let else_stream = [L(else_lbl)] >@ e_stream >:: jmp_to_post in
    c, [jmp_to_start] >@ start_stream >@ then_stream >@ else_stream >:: L(post_lbl)
  | SCall(fn, args) ->
    let call_node = no_loc @@ Call(fn, args) in
    let _, _, stream = cmp_exp c call_node  in
    c, stream
  | _ -> failwith "cmp_stmt not implemented"
and cmp_stmts (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : stream = snd @@ cmp_stmts c rt stmts 

(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
        let ft = TRef (RFun (List.map fst args, frtyp)) in
        Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
      | Ast.Gvdecl { elt = {name; init} } -> (
          let ty = match init.elt with
            | CBool _       -> Ptr I1
            | CInt _        -> Ptr I64
            | CStr s        -> Ptr (Array (1 + String.length s, I8))
            (* | CNull ty      -> Ptr (cmp_ty ty)
               | CArr (ty, _)  -> Ptr (Struct [I64; Array(0, cmp_ty ty)]) *)
            | _ -> failwith "unsupported type"
          in
          Ctxt.add c name (ty, Gid name)
        )
      | _ -> c
    ) c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   3. Compile the body of the function using cmp_block
   4. Use cfg_of_stream to produce a LLVMlite cfg from 
*)
let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let f = f.elt in
  let frtyp = cmp_ret_ty f.frtyp in
  let fptyp = f.args |> List.map (fun (ty, _) -> cmp_ty ty) in
  let f_ty = fptyp, frtyp in
  let f_param = f.args |> List.map (fun (_, uid) -> uid) in
  let c, f_param_stream = f.args |> List.fold_left (fun (c, stream) (ty, id) ->
      let ty = cmp_ty ty in
      let uid = gensym id in
      let c = Ctxt.add c id (Ptr ty, Id uid) in
      c, stream >:: E(uid, Alloca ty) >:: I("", Store(ty, Id id, Id uid))
    ) (c, [])
  in
  let body_stream = f.body |> cmp_block c frtyp in
  let (f_cfg, gs) = cfg_of_stream (f_param_stream >@ body_stream) in
  {f_ty; f_param; f_cfg}, gs

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations
*)
let rec cmp_gexp (c : Ctxt.t) (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CBool b ->  (I1, GInt(if b then Int64.one else Int64.zero)), []
  | CInt i ->  (I64, GInt i), []
  | CStr s ->  (Array (1 + String.length s, I8), GString s), []
  (* | CNull ty      ->  (Ptr (cmp_ty ty), GNull),   [] *)
  (* | CArr(ty, es)  -> *)
  | _ -> failwith "cmp_init not implemented"


(* Oat internals function context ------------------------------------------- *)
let internals = [
  "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
          let ll_gd, gs' = cmp_gexp c gd.init in
          (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
          let fdecl, gs' = cmp_fdecl c fd in
          (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
