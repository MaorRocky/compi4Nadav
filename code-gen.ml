#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

let just_ret_unit = fun x -> ()

let car = fun x y -> x

let rec rename_tags_all_asts asts num =
  let rec rename_tags_sexp sexp str_num =
    match sexp with
    | Pair(car, cdr) -> Pair((rename_tags_sexp car str_num), (rename_tags_sexp cdr str_num))
    | TaggedSexpr(tag, sexpr) -> (let new_tag = ""^tag^""^str_num^"" in
                                  TaggedSexpr(new_tag, (rename_tags_sexp sexpr str_num)))
    | TagRef(tag) -> (let new_tag = ""^tag^""^str_num^"" in
                      TagRef(new_tag))
    | _ -> sexp in
  let rec rename_tags_ast str_num ast = 
    match ast with
    | Const'(Sexpr(sexp)) -> Const'(Sexpr(rename_tags_sexp sexp str_num))
    | BoxSet'(var, expr') -> BoxSet'(var, (rename_tags_ast str_num expr'))
    | If'(test, dit, dif) -> If'((rename_tags_ast str_num test), (rename_tags_ast str_num dit), (rename_tags_ast str_num dif))
    | Seq'(exprs) -> Seq'(List.map (rename_tags_ast str_num) exprs)
    | Set'(set_var, set_val) -> Set'((rename_tags_ast str_num set_var), (rename_tags_ast str_num set_val))
    | Def'(def_var, def_val) -> Def'((rename_tags_ast str_num def_var), (rename_tags_ast str_num def_val))
    | Or'(exprs) -> Or'(List.map (rename_tags_ast str_num) exprs)
    | LambdaSimple'(params, body) -> LambdaSimple'(params, (rename_tags_ast str_num body))
    | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (rename_tags_ast str_num body))
    | Applic'(operator, args) -> Applic'((rename_tags_ast str_num operator), (List.map (rename_tags_ast str_num) args))
    | ApplicTP'(operator, args) -> ApplicTP'((rename_tags_ast str_num operator), (List.map (rename_tags_ast str_num) args))
    | _ -> ast in
  match asts with
  | ast :: rest -> (rename_tags_ast (string_of_int num) ast) :: (rename_tags_all_asts rest (num + 1))
  | [] -> asts;;

let rec get_all_sexps expr'=
  let global_lst = ref [] in
  let rec func expr' = 
    match expr' with
    | Const'(Sexpr(sexp)) -> (let a = global_lst := List.append !global_lst [sexp] in
                       just_ret_unit a)
    | Const'(Void) -> ()
    | Var'(var) -> ()
    | Box'(var) -> ()
    | BoxGet'(var) -> ()
    | BoxSet'(var, expr) -> (func expr)
    | If'(test, dit, dif) -> (just_ret_unit (List.map func [test; dit; dif])) 
    | Seq'(exprs) -> (just_ret_unit (List.map func exprs))
    | Set'(set_var, set_val) -> (just_ret_unit (List.map func [set_var; set_val]))
    | Def'(def_var, def_val) -> (just_ret_unit (List.map func [def_var; def_val]))
    | Or'(exprs) -> (just_ret_unit (List.map func exprs))
    | LambdaSimple'(params, body) -> (just_ret_unit (func body))
    | LambdaOpt'(params, opt_param, body) -> (just_ret_unit (func body))
    | Applic'(operator, args) -> (let a = [func operator] in
                                  let b = List.map func args in
                                  just_ret_unit [a; b])
    | ApplicTP'(operator, args) -> (let a = [func operator] in
                                    let b = List.map func args in
                                    just_ret_unit [a; b]) in
    
  let just_a_unit = func expr' in
  car !global_lst just_a_unit
  ;;

let get_all_sexp_multiple_asts asts = 
  let list_of_sexp_lists = List.map get_all_sexps asts in
  List.flatten list_of_sexp_lists;;

let unique_cons xs x = 
  if List.mem x xs 
  then xs
  else x :: xs

let remove_dups_from_left xs = 
  List.rev (List.fold_left unique_cons [] xs)

let rec expand_sexp sexp = 
  match sexp with
  | Nil -> []
  | Bool(false) -> []
  | Bool(true) -> []
  | Symbol(a) -> [String(a); Symbol(a)]
  | TaggedSexpr(name, sexpr) -> expand_sexp sexpr
  | Pair(a, b) -> List.append (List.append (expand_sexp a) (expand_sexp b)) [sexp]
  | _ -> [sexp];;

let rec expand_list lst = 
  if List.length lst = 0
  then lst
  else List.append (expand_sexp (List.hd lst)) (expand_list (List.tl lst))

let rec find_sexp_by_ref_name ref_name tuple_lst index = 
  match tuple_lst with
  | (name, sexp) :: rest when ref_name = name -> index
  | (name, sexp) :: rest -> find_sexp_by_ref_name ref_name rest (index + 1) 
  | [] -> (-1)

let rec from_sexp_lst_to_const_tbl tagged_tuple_lst lst =
  let global_lst = ref [(Void, (0, "MAKE_VOID")); (Sexpr(Nil), (1, "MAKE_NIL"));
                        (Sexpr(Bool(false)), (2, "MAKE_BOOL(0)")); (Sexpr(Bool(true)), (4, "MAKE_BOOL(1)"))] in
  let rec get_offset_of_sexp_2 sexp const_tbl = 
    match const_tbl with
    | (Sexpr(sexpr), (offset, representation)) :: rest when (sexpr_eq sexpr sexp) -> offset
    | tuple :: rest -> get_offset_of_sexp_2 sexp rest
    | [] -> (-1) in
  let get_tag_ref_offset_2 name = 
    let index = find_sexp_by_ref_name name tagged_tuple_lst 0 in
    if index = (-1)
    then (raise X_this_should_not_happen)
    else (let (ref_name, sexpr) = List.nth tagged_tuple_lst index in
          get_offset_of_sexp_2 sexpr !global_lst) in
  let add_next_tuple sexp =
    let rec get_offset_of_sexp sexp const_tbl = 
        match const_tbl with
        | (Sexpr(sexpr), (offset, representation)) :: rest when (sexpr_eq sexpr sexp) -> offset
        | tuple :: rest -> get_offset_of_sexp sexp rest
        | [] -> (-1) in
    let get_tag_ref_offset name = 
      let index = find_sexp_by_ref_name name tagged_tuple_lst 0 in
      if index = (-1)
      then (raise X_this_should_not_happen)
      else (let (ref_name, sexpr) = List.nth tagged_tuple_lst index in
            get_offset_of_sexp sexpr !global_lst) in
    let get_next_offset =
        let last_tuple = List.nth !global_lst ((List.length !global_lst) - 1) in
        match last_tuple with
        | (Void, (offset, representation)) -> offset + 1 (*this should not happen*) 
        | (Sexpr(Nil), (offset, representation)) -> offset + 1 (*this should not happen*) 
        | (Sexpr(Bool(_)), (offset, representation)) -> offset + 2
        | (Sexpr(Char(_)), (offset, representation)) -> offset + 2
        | (Sexpr(Number(_)), (offset, representation)) -> offset + 9
        | (Sexpr(String(str)), (offset, representation)) -> offset + 9 + (String.length str)
        | (Sexpr(Symbol(str)), (offset, representation)) -> offset + 9
        | (Sexpr(Pair(car, cdr)), (offset, representation)) -> offset + 17 
        | (Sexpr(TaggedSexpr(name, sepxr)), (offset, representation)) -> offset (*this should not happen*)
        | (Sexpr(TagRef(name)), (offset, representation)) -> offset (*this should not happen*) in
    let offset = (get_next_offset) in
    match sexp with
    | Bool(true) -> (global_lst := !global_lst)
    | Bool(false) -> (global_lst := !global_lst)
    | Nil -> (global_lst := !global_lst)
    | Number(Int(num)) -> (global_lst := List.append !global_lst [(Sexpr(sexp), (offset, "MAKE_LITERAL_INT("^string_of_int num^")"))])
    | Number(Float(num)) -> (global_lst := List.append !global_lst [(Sexpr(sexp), (offset, "MAKE_LITERAL_INT("^string_of_float num^")"))])
    | Char(ch) -> (global_lst := List.append !global_lst 
                                        [(Sexpr(sexp), (offset, "MAKE_LITERAL_CHAR("^string_of_int(int_of_char(ch))^")"))])
    | String(str) -> (global_lst := List.append !global_lst [(Sexpr(sexp), (offset, "MAKE_LITERAL_STRING("^str^")"))])
    | Symbol(str) -> (let symbol_offset = get_offset_of_sexp (String(str)) !global_lst in
                      global_lst := List.append !global_lst 
                                [(Sexpr(sexp), (offset, "MAKE_LITERAL_SYMBOL(consts+"^string_of_int(symbol_offset)^")"))])
    | Pair(car, cdr) -> (let car_offset = (match car with
                                           | TaggedSexpr(name, sexp1) -> string_of_int(get_offset_of_sexp sexp1 !global_lst)
                                           | TagRef(name) -> (string_of_int((get_tag_ref_offset name)))
                                           | _ -> string_of_int(get_offset_of_sexp car !global_lst)) in
                         let cdr_offset = (match cdr with
                                           | TaggedSexpr(name, sexp1) -> string_of_int(get_offset_of_sexp sexp1 !global_lst)
                                           | TagRef(name) -> string_of_int((get_tag_ref_offset name))
                                           | _ -> string_of_int(get_offset_of_sexp cdr !global_lst)) in
                         global_lst := List.append !global_lst 
                                        [(Sexpr(sexp), (offset, "MAKE_LITERAL_PAIR(consts+"^car_offset^", consts+"^cdr_offset^")"))])
    | _ -> global_lst := List.append !global_lst [] in
  let rec repair_tag_refs_offsets const_tbl = 
    match const_tbl with
    | (Sexpr(Pair(car, TagRef(name))), (offset, str)) :: rest ->
        (let str_tag_ref_offset = string_of_int((get_tag_ref_offset_2 name)) in
        match car with
        | TaggedSexpr(name, sexpr) ->
          (Sexpr(Pair(car, TagRef(name))), (offset, "MAKE_LITERAL_PAIR(consts+"^string_of_int((get_offset_of_sexp_2 sexpr !global_lst))^", consts+"^str_tag_ref_offset^")")) :: 
          (repair_tag_refs_offsets rest)
        | _ ->
          (Sexpr(Pair(car, TagRef(name))), (offset, "MAKE_LITERAL_PAIR(consts+"^string_of_int((get_offset_of_sexp_2 car !global_lst))^", consts+"^str_tag_ref_offset^")")) :: 
          (repair_tag_refs_offsets rest))
    | tuple :: rest -> tuple :: (repair_tag_refs_offsets rest)
    | [] -> [] in
  let dont_care = List.map add_next_tuple lst in
  let ret = repair_tag_refs_offsets !global_lst in
  car ret dont_care;;

let collect_all_tagged_sexps sexp_lst = 
  let tagged_sexps = ref [] in
  let rec collect lst = 
    match lst with
    | TaggedSexpr(name, sexp) :: rest -> (let a = tagged_sexps := List.append !tagged_sexps [(name, sexp)] in
                                          if a = ()
                                          then (collect (List.append [sexp] rest))
                                          else ())
    | Pair(car, cdr) :: rest -> collect (List.append [car; cdr] rest)
    | sexp :: rest -> collect rest
    | [] -> () in
  let just_a_unit = collect sexp_lst in
  car !tagged_sexps just_a_unit;;

(*let my_func = fun str -> 
  let from_sexp_lst_to_const_tbl (remove_dups_from_left (expand_list (remove_dups_from_left (get_all_sexps (my_run (my_tag (my_read_sexpr str)))))))*)

let check_tags = fun str ->
  let sexps_list = get_all_sexp_multiple_asts (rename_tags_all_asts (my_runs (my_tags (my_read_sexprs str))) 0) in
  let tagged_tuples_list = collect_all_tagged_sexps sexps_list in
  let expanded_sexps_list = remove_dups_from_left (expand_list sexps_list) in
  from_sexp_lst_to_const_tbl tagged_tuples_list expanded_sexps_list
  (*from_sexp_lst_to_const_tbl (remove_dups_from_left (expand_list (remove_dups_from_left (get_all_sexp_multiple_asts (rename_tags_all_asts (my_runs (my_tags (my_read_sexprs str))))))))*)

(* get_all_sexps (boxing (tail_cals false (lexical_addresses [] [] false ()))) *)


let rec get_all_freeVars expr'=
  let global_lst = ref [] in
  let rec func expr' = 
    match expr' with
    | Var'(VarFree(var)) -> (let a = global_lst := List.append !global_lst [var] in
                             just_ret_unit a)
    | Const'(Sexpr(sexp)) -> ()
    | Const'(Void) -> ()
    | Box'(var) -> ()
    | BoxGet'(var) -> ()
    | BoxSet'(var, expr) -> (func expr)
    | If'(test, dit, dif) -> (just_ret_unit (List.map func [test; dit; dif])) 
    | Seq'(exprs) -> (just_ret_unit (List.map func exprs))
    | Set'(set_var, set_val) -> (just_ret_unit (List.map func [set_var; set_val]))
    | Def'(def_var, def_val) -> (just_ret_unit (List.map func [def_var; def_val]))
    | Or'(exprs) -> (just_ret_unit (List.map func exprs))
    | LambdaSimple'(params, body) -> (just_ret_unit (func body))
    | LambdaOpt'(params, opt_param, body) -> (just_ret_unit (func body))
    | Applic'(operator, args) -> (let a = [func operator] in
                                  let b = List.map func args in
                                  just_ret_unit [a; b])
    | ApplicTP'(operator, args) -> (let a = [func operator] in
                                    let b = List.map func args in
                                    just_ret_unit [a; b]) in

  let just_a_unit = func expr' in
  car !global_lst just_a_unit
;;

let create_free_vars_table asts =
  let initial_fvars =[("boolean?",0); ("float?",1); ("integer?",2);
                      ("pair?",3);("null?",4);("char?",5); ("vector?",6); ("string?",7);
                      ("procedure?",8); ("symbol?",9);  ("string-length",10) ;
                      ("string-ref",11) ; ( "string-set!",12); ("make-string",13);
                      ("vector-length",14); ("vector-ref",15); ("vector-set!",16);
                      ("make-vector",17);("symbol->string",18);("char->integer",19); 
                      ("integer->char",20);  ("eq?",21);
                      ("+",22); ("*",23); ("-",24); ("/",25); ("<",26 ); ("=",27);
                      ("car",28); ("cdr",29);("set-car!",30);("set-cdr!",31); ("apply",32);("cons",33);
                     ] in
  let rec add_fvar_tuple fvars_to_add fvar_table index=
    if List.length fvars_to_add < 1 (* Break *)
    then fvar_table
    else(
      let head_fvar = List.hd fvars_to_add in
      let fvar_table_names = List.map (fun (name,_)-> name) fvar_table in
      if List.mem head_fvar fvar_table_names (* no need to add this fvar*)
      then (add_fvar_tuple (List.tl fvars_to_add) fvar_table index) (* continue *)
      else (* adding the fvar *)
        (let newFvarTuple = (head_fvar,index) in
         add_fvar_tuple (List.tl fvars_to_add) (List.append fvar_table [newFvarTuple]) (index + 1)))
  in
  let fvars_from_ast = (remove_dups_from_left(get_all_freeVars asts)) in
  (add_fvar_tuple fvars_from_ast initial_fvars 34);;
;; 
(* find index of free var in fvars_table *)
let rec getIndex_fvars fvars_table fvar_name =
  if List.length fvars_table < 1 
  then -1
  else
    let (name,fvar_index) = (List.hd fvars_table) in
    if(String.equal name fvar_name) 
    then fvar_index
    else getIndex_fvars (List.tl fvars_table) fvar_name ;;
(* NADAV you might need to change it im not sure how const table is set up *)

let getIndex_const_table const const_table =
  let (sexp, (offset, str)) =  
    (List.find (fun (sexp, (address,str)) -> sexpr_eq sexp const) const_table) in
  index;;

(* global index *)
let index = ref 0;;

let increment_index =
  fun () -> index := !index + 1 in
            !index - 1;;
(* the main method 
   im not sure about the paremeters of the function*)
let  generate consts fvars e  =
  (* will be used to help us with applic *)
  (* let rec applic_helper lst i =
     if List.length lst < 1 
     then ""
     else
      (mainGenerate (List.hd lst) i )^"push rax\n"^(applic_helper (List.tl lst) i) 
  *)
  let rec or_helper lst e' ind env =
    if List.length lst < 1 
    then "Lexit"^(string_of_int ind)^":\n" 
    else
    if  List.length lst = 1 
    then (mainGenerate (List.hd lst) env)^(or_helper( (List.tl lst)) e' ind env)
    else
      (mainGenerate (List.hd lst) env)^"cmp rax, sob_false\njne Lexit"^(string_of_int ind)^"\n"^(or_helper ((List.tl lst)) e' ind env)

  and if_helper test dit dif env ind =
    (mainGenerate test env) ^ "\n" ^
    "cmp rax, SOB_FALSE_ADDRESS\n" ^
    "je Lelse_" ^ (string_of_int ind) ^ "\n" ^  
    (mainGenerate dit env) ^ "\n" ^
    "jmp Lexit_" ^ (string_of_int ind) ^ "\n" ^
    "Lelse_" ^ (string_of_int ind) ^ ":\n" ^
    (mainGenerate dif env) ^ "\n" ^
    "Lexit_" ^ (string_of_int ind) ^ ":\n"

  and lambda_helper params body env = (*  NADAV PUT COMMENTS *)
    let ind = increment_index() in
    let extend = 
      if env < 1
      then   
        "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode"^(string_of_int ind)^")\n
        jmp Lcont"^(string_of_int ind)^"\n
        Lcode"^(string_of_int ind)^":\n
        push rbp\n
        mov rbp, rsp\n
        "^(mainGenerate body (env+1))^"
        leave\n
        ret\n
        Lcont"^(string_of_int ind)^":\n"  
      else
        "MALLOC rbx, "^(string_of_int env)^" * WORD_SIZE
        mov qword rcx, [rbp+16] ; now rcx holds a pointer to the env
        mov rdx, "^(string_of_int env)^" ; depth of the env is now in rdx, will be used in loop counter
        dec rdx
        mov r10, 0 ; will use r10 to compare to 0
        mov r9,1 ; will use r9 to multiply by 8
        .loop: 
          cmp r10, rdx
          je .loop_end
          mov qword r11, [rcx+8*r9]
          mov qword [rbx+8*r9], r11
          inc r9
          dec rdx
          jmp .loop
        .loop_end:
          mov qword r8, [rbp+24] ; r8 hold the args count
          shl r8 3 ; n:=n*8 
          MALLOC rax, r8
          mov qword [rbx], rax 
          mov rdx, r8 ; rdx holds the args count * 8, will be used in the loop
        .create_loop:
          cmp r10, rdx
          je jmp .end_create_loop
          mov qword r12, [rbp + 8 * (4+r10)]
          mov qword [rax + **r10], r12
          inc r10
          jmp .create_loop
        .end_create_loop:
        MAKE_CLOSURE(rax, rbx, Lcode"^(string_of_int ind)^")
        jmp Lcont"^(string_of_int ind)^"
        Lcode"^(string_of_int ind)^":
        push rbp
        mov rbp, rsp
        "^(mainGenerate body (env+1))^"
        leave
        ret
        Lcont"^(string_of_int ind)^":\n"


    and mainGenerate e env = 
      match e with        
      | Const'(Sexpr(c)) -> let i = (getIndex_const_table c consts) in "mov rax, const_tbl+"^(string_of_int i)^"\n"
      | Var'(VarParam(_, minor)) -> "mov qword rax, [rbp + "^(string_of_int (8*(minor+4)))^"]\n"
      | Set'(Var'(VarParam(_, minor)), e') ->   (* NOT THE SAME AS e as e' *)
        (mainGenerate e' env) ^"mov qword [rbp + "^(string_of_int (8*(4+minor)))^"], rax\nmov rax, sob_void\n"
      | Var'(VarBound(_, major, minor)) ->
        "mov rax, qword [rbp + 16]\n"^
        "mov rax, qword [rax + "^(string_of_int (major*8))^"]\n"^
        "mov rax, qword [rax + "^(string_of_int (minor*8))^"]\n"
      | Set'(Var'(VarBound(_, major, minor)), e') ->
        (mainGenerate e' env)^
        "mov rbx, qword [rbp + 8 ∗ 2]\n"^
        "mov rbx, qword [rbx + 8 ∗"^(string_of_int major)^"]\n"^
        "mov qword [rbx + 8 ∗"^(string_of_int minor)^"], rax\n"^
        "mov rax, sob_void\n"
      | Set'(Var'(VarFree(s)), e') -> (mainGenerate e' env)^
                                      "mov qword [fvar_tbl+"^(string_of_int (8*(getIndex_fvars fvars s)))^"], rax\nmov rax, sob_void\n"
      |Var'(VarFree(v)) -> "mov rax, qword [fvar_tbl + "^(string_of_int (8*(getIndex_fvars fvars v)))^"]\n"
      |Seq' (lst) -> List.fold_left (fun acc curr -> acc ^ "\n" ^ (mainGenerate curr env) ^ "\n") "" lst 
      |Or'(lst) -> let ind = increment_index () in (or_helper lst e ind env)
      |If' (test, dit, dif) -> 
        let ind = increment_index () in
        (if_helper test dit dif env ind)
      |BoxGet' (v) -> (mainGenerate (Var'(v)) env)  ^ "\n" ^
                      "mov rax, qword [rax]\n"
      |BoxSet' (v, e') -> (mainGenerate e' env) ^ "\n" ^
                          "push rax\n" ^
                          (mainGenerate (Var'(v)) env) ^ "\n" ^
                          "pop qword [rax]\n" ^ 
                          "mov rax, sob_void\n"
      |LambdaSimple'(params, body) -> lambda_helper params body env
    in mainGenerate e 0;;



let make_consts_tbl_2 asts = 
    let sexps_list = get_all_sexp_multiple_asts (rename_tags_all_asts asts 0) in
    let tagged_tuples_list = collect_all_tagged_sexps sexps_list in
    let expanded_sexps_list = remove_dups_from_left (expand_list sexps_list) in
    from_sexp_lst_to_const_tbl tagged_tuples_list expanded_sexps_list;;


module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = 
    let sexps_list = get_all_sexp_multiple_asts (rename_tags_all_asts asts 0) in
    let tagged_tuples_list = collect_all_tagged_sexps sexps_list in
    let expanded_sexps_list = remove_dups_from_left (expand_list sexps_list) in
    from_sexp_lst_to_const_tbl tagged_tuples_list expanded_sexps_list;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

