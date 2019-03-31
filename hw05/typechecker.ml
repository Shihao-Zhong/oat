open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))

let pp = Printf.sprintf

(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TNullRef(rty1), TNullRef(rty2)
  | TRef(rty1), TRef(rty2)
  | TRef(rty1), TNullRef(rty2) -> subtype_ref c rty1 rty2
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true
  | RArray t1, RArray t2 -> t1 = t2
  | RStruct id1, RStruct id2 -> subtype_struct c id1 id2
  | RFun(args, ret), RFun(args', ret') -> subtype_func c args ret args' ret'
  | _ -> false

(* Decides whether H |-r ret_ty1 <: ret_ty2 *)
and subtype_ret_ty (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVal(t1), RetVal(t2) -> subtype c t1 t2
  | _ -> false

and subtype_func c args ret args' ret' : bool = 
  let args_pred = List.length args = List.length args' in
  let args_pred = args_pred && List.fold_left2(fun acc arg arg' -> acc && subtype c arg' arg) true args args' in
  let ret_pred = subtype_ret_ty c ret ret' in
  args_pred && ret_pred

and subtype_struct c s1 s2 : bool = s1 = s2 ||
  match Tctxt.lookup_struct_option s2 c with
  | None -> false
  | Some s2_fields ->
    List.fold_left (fun acc field -> acc && 
      let res = Tctxt.lookup_field_option s1 field.fieldName c in
      match res with
      | None -> false
      | Some t -> t = field.ftyp
    ) true s2_fields
  
(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is 

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TRef(rty) | TNullRef(rty) -> typecheck_ref_ty l tc rty
and typecheck_ref_ty  (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray ty -> typecheck_ty l tc ty
  | RStruct id -> (
    match Tctxt.lookup_struct_option id tc with
    | None -> type_error l (pp "undefined struct %s" id)
    | Some _ -> ()
  )
  | RFun(params, ret_ty) -> (
    List.iter (fun p -> typecheck_ty l tc p) params;
    typecheck_ret_ty l tc ret_ty;
  )
and typecheck_ret_ty  (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal ty -> typecheck_ty l tc ty

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull(rty) -> (
    typecheck_ref_ty e c rty;
    TNullRef(rty)
  )
  | CBool _-> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef(RString)
  | Id id -> (
    match (Tctxt.lookup_option id c) with
    | None -> type_error e (pp "undefined Identifier %s" id)
    | Some ty -> ty
  )
  | CArr(ty, es) -> (
    typecheck_ty e c ty;
    let exp_tys = List.map (fun e -> typecheck_exp c e) es in
    let init_pred = List.fold_left (fun acc t -> acc && subtype c t ty) true exp_tys in
    match init_pred with
    | false -> type_error e "unexpected array element type"
    | true -> TRef(RArray(ty))
  )
  | NewArr(ty, len, id, init) -> (
    typecheck_ty e c ty;
    let len_pred = typecheck_exp c len = TInt in
    let id_pred = match Tctxt.lookup_local_option id c with None -> true | Some _ -> false in
    let init_exp_ty = typecheck_exp (Tctxt.add_local c id TInt) init in
    let init_pred = subtype c init_exp_ty ty in
    match len_pred, id_pred, init_pred with
    | true, true, true -> TRef(RArray(ty))
    | false, _, _ -> type_error e "expected a length of type Int"
    | _, false, _ -> type_error e (pp "array init identifier [%s] is defined in the local context" id)
    | _, _, false -> type_error e (pp "expected an init expression of type %s" @@ string_of_ty ty)
  )
  | Index(arr, ind) -> (
    let ind_ty = typecheck_exp c ind in
    let arr_ty = typecheck_exp c arr in
    match arr_ty, ind_ty with
    | TRef(RArray(ty)), TInt -> ty
    | TRef(RArray(_)), ty -> type_error e (pp "expected an index of type Int but if found a %s" @@ string_of_ty ty)
    | ty, TInt -> type_error e (pp "expected an expression of type TRef(TArray(t)) but it found a %s" @@ string_of_ty ty)
    | _, _ -> type_error e "both the expression and index have incorrect types"
  )
  | Length(arr) -> (
    let arr_ty = typecheck_exp c arr in
    match arr_ty with
    | TRef(RArray(_))-> TInt
    | ty -> type_error e (pp "expected an expression of type TRef(RArray(ty)) but it found a %s" @@ string_of_ty ty)
  )
  | CStruct(s_id, fields) -> (
    let fields_subtype_pred = List.fold_left(fun acc (f_id, f_init_exp) -> acc &&
      let f_init_ty = typecheck_exp c f_init_exp in
      match Tctxt.lookup_field_option s_id f_id c with
      | None -> false
      | Some f_ty -> subtype c f_init_ty f_ty
    ) true fields in
    let expected_struct_fields = Tctxt.lookup_struct s_id c in
    let all_fields_present_pred = List.fold_left(
      fun acc f -> acc && List.exists (fun (id, _) -> id = f.fieldName) fields
    ) true expected_struct_fields in
    match fields_subtype_pred, all_fields_present_pred with
    | true, true -> TRef(RStruct s_id)
    | false, _ -> type_error e "expression does not have the correct field type"
    | _, false -> type_error e "you need to initialize all the struct fields"
  )
  | Proj(s, f_id) -> (
    let s_ty = typecheck_exp c s in
    match s_ty with
    | TRef(RStruct s_id) -> (
      let f_ty = Tctxt.lookup_field_option s_id f_id c in
      match f_ty with
      | None -> type_error e (pp "undefined field %s" f_id)
      | Some ty -> ty
    )
    | ty -> type_error e (pp "expected an expression of type struct but it received a %s" @@ string_of_ty ty)
  )
  | Call(fun_id, args) -> (
    let params, ret_ty = match typecheck_exp c fun_id with
    | TRef(RFun(params, ret_ty)) -> params, ret_ty
    | ty -> type_error e (pp "identifier of type %s is not a function" @@ string_of_ty ty) in

    let args_ty = List.map(fun arg -> typecheck_exp c arg) args in
    let args_ty_pred = List.fold_left2(fun acc param arg -> acc && subtype c arg param) true params args_ty in
    let arg_len_pred = List.length params = List.length args in

    match args_ty_pred, arg_len_pred, ret_ty with
    | true, true, RetVal(ret_ty)  -> ret_ty
    | false, _, _ -> type_error e "unexpected argument types in function call"
    | _, false, _ -> type_error e "unexpected number of arguments"
    | _, _, RetVoid -> type_error e "todo: how to handle function returning Void -_-"
  )
  | Bop (Neq, l, r)
  | Bop (Eq, l, r) -> (
    let l_ty = typecheck_exp c l in
    let r_ty = typecheck_exp c r in
    match subtype c l_ty r_ty, subtype c r_ty l_ty with
    | true, true -> TBool
    | false, _ -> type_error e (pp "a left operand of type %s is not a subtype of a right operand of type %s" (string_of_ty l_ty) (string_of_ty r_ty))
    | _, false -> type_error e (pp "a right operand of type %s is not a subtype of a left operand of type %s" (string_of_ty r_ty) (string_of_ty l_ty))
  )
  | Bop (biop, l, r) -> (
    let l_ty, r_ty, ret_ty = typ_of_binop biop in
    let l_pred = typecheck_exp c l = l_ty in
    let r_pred = typecheck_exp c r = r_ty in
    match l_pred, r_pred with
    | true, true -> ret_ty
    | false, _ -> type_error e (pp "expected left operand to have type %s" @@ string_of_ty l_ty)
    | _, false -> type_error e (pp "expected right operand to have type %s" @@ string_of_ty l_ty)
  ) 
  | Uop (uop, exp) -> (
    let exp_ty, ret_ty = typ_of_unop uop in
    let exp_pred = typecheck_exp c exp = exp_ty in
    match exp_pred with
    | true -> ret_ty
    | false -> type_error e (pp "expected a operand of type %s" @@ string_of_ty exp_ty)
  )

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  failwith "todo: implement typecheck_stmt"


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  failwith "todo: typecheck_fdecl"

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'F' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_struct_ctxt"

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
