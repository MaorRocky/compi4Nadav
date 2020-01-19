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

(*General*)

let just_ret_unit = fun x -> ()

let car = fun x y -> x

(*END OF GENERAL*)

(*CONSTANTS TABLE*)

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
    | String(str) -> (global_lst := List.append !global_lst [(Sexpr(sexp), (offset, "MAKE_LITERAL_STRING \""^str^"\","^string_of_int(String.length str)^""))])
    | Symbol(str) -> (let symbol_offset = get_offset_of_sexp (String(str)) !global_lst in
                      global_lst := List.append !global_lst 
                                [(Sexpr(sexp), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^string_of_int(symbol_offset)^")"))])
    | Pair(car, cdr) -> (let car_offset = (match car with
                                           | TaggedSexpr(name, sexp1) -> string_of_int(get_offset_of_sexp sexp1 !global_lst)
                                           | TagRef(name) -> (string_of_int((get_tag_ref_offset name)))
                                           | _ -> string_of_int(get_offset_of_sexp car !global_lst)) in
                         let cdr_offset = (match cdr with
                                           | TaggedSexpr(name, sexp1) -> string_of_int(get_offset_of_sexp sexp1 !global_lst)
                                           | TagRef(name) -> string_of_int((get_tag_ref_offset name))
                                           | _ -> string_of_int(get_offset_of_sexp cdr !global_lst)) in
                         global_lst := List.append !global_lst 
                                        [(Sexpr(sexp), (offset, "MAKE_LITERAL_PAIR(const_tbl+"^car_offset^", const_tbl+"^cdr_offset^")"))])
    | _ -> global_lst := List.append !global_lst [] in
  let rec repair_tag_refs_offsets const_tbl = 
    match const_tbl with
    | (Sexpr(Pair(car, TagRef(name))), (offset, str)) :: rest ->
        (let str_tag_ref_offset = string_of_int((get_tag_ref_offset_2 name)) in
        match car with
        | TaggedSexpr(name, sexpr) ->
          (Sexpr(Pair(car, TagRef(name))), (offset, "MAKE_LITERAL_PAIR(const_tbl"^string_of_int((get_offset_of_sexp_2 sexpr !global_lst))^", const_tbl"^str_tag_ref_offset^")")) :: 
          (repair_tag_refs_offsets rest)
        | _ ->
          (Sexpr(Pair(car, TagRef(name))), (offset, "MAKE_LITERAL_PAIR(const_tbl"^string_of_int((get_offset_of_sexp_2 car !global_lst))^", const_tbl"^str_tag_ref_offset^")")) :: 
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


let rec getOffset_const_table const const_table = 
  match const_table with
  | tuple :: rest -> (match tuple with
                      | (Sexpr(sexp), (offset, str)) -> (if (sexpr_eq const sexp)
                                                         then offset
                                                         else (getOffset_const_table const rest))
                      | (Void, (offset, str)) -> (getOffset_const_table const rest))
  | [] -> (-1);; 


(*END OF CONSTANTS TABLE*)

(*FREE-VARS TABLE*)

let rec get_all_freeVars expr'=
  let global_lst = ref [] in
  let rec func expr' = 
    match expr' with
    | Var'(VarFree(var)) -> (let a = global_lst := List.append !global_lst [var] in
                             just_ret_unit a)
    | Var'(var) -> ()
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

let get_all_fvars_multiple_asts asts = 
  let list_of_fvars_lists = List.map get_all_freeVars asts in
  List.flatten list_of_fvars_lists;;

let getIndex_fvars fvars_table fvar_name =
  try 
    (let (name, index) = List.find (fun (name, index) -> String.equal fvar_name name) fvars_table in
     index)
  with Not_found -> (-1);;

let create_free_vars_table asts =
  let initial_fvars = [("boolean?",0); ("float?",1); ("integer?",2);
                       ("pair?",3);("null?",4);("char?",5); ("string?",6);
                       ("procedure?",7); ("symbol?",8);  ("string-length",9) ;
                       ("string-ref",10) ; ( "string-set!",11); ("make-string",12);
                       ("symbol->string",13);("char->integer",14); 
                       ("integer->char",15);  ("eq?",16);
                       ("+",17); ("*",18); ("-",19); ("/",20); ("<",21); ("=",22);
                       ("car",23); ("cdr",24); ("cons", 25); ("set-car!",26);("set-cdr!",27); ("apply",28)
                      ] in
  let rec add_fvars_tuples fvars_table fvars_list_to_add = 
    let add_single_tuple fvar_list fvar = 
      let index = getIndex_fvars fvar_list fvar in
      if index = (-1) 
      (*there is no free var with that name in the current fvars table, hence adding it to the table*)
      then List.append fvar_list [(fvar, (List.length fvar_list))]
      else fvar_list in
    match fvars_list_to_add with
    | fvar_name :: rest -> add_fvars_tuples (add_single_tuple fvars_table fvar_name) rest
    | [] -> fvars_table in
  let fvars_from_ast = remove_dups_from_left (get_all_fvars_multiple_asts asts) in
  add_fvars_tuples initial_fvars fvars_from_ast;;


let rec my_generate consts fvars e = 
  match e with
  | Const'(Sexpr(expr)) -> (let str_offset = string_of_int (getOffset_const_table expr consts) in
                            "mov rax, const_tbl+"^str_offset^"")
  | _ -> "mov rax, 1"


let make_consts_tbl_2 asts =
  let sexps_list = get_all_sexp_multiple_asts (rename_tags_all_asts asts 0) in
  let tagged_tuples_list = collect_all_tagged_sexps sexps_list in
  let expanded_sexps_list = remove_dups_from_left (expand_list sexps_list) in
  from_sexp_lst_to_const_tbl tagged_tuples_list expanded_sexps_list;;

let check_const_table = fun str ->
  let sexps_list = get_all_sexp_multiple_asts (rename_tags_all_asts (my_runs (my_tags (my_read_sexprs str))) 0) in
  let tagged_tuples_list = collect_all_tagged_sexps sexps_list in
  let expanded_sexps_list = remove_dups_from_left (expand_list sexps_list) in
  from_sexp_lst_to_const_tbl tagged_tuples_list expanded_sexps_list;;

let check_fvar_table = fun str ->
  let asts = my_runs (my_tags (my_read_sexprs str)) in
  create_free_vars_table asts;;

let asts = fun str ->
  my_runs (my_tags (my_read_sexprs str))

let random_str_num stam = 
  let num = (Random.int 999999999) in
  string_of_int(num);;

let rec main_generate consts fvars depth expr' =
  match expr' with
  | Const'(Sexpr(expr)) -> (let str_offset = string_of_int (getOffset_const_table expr consts) in
                              "mov rax, const_tbl+"^str_offset^"\n")
  | Seq' (lst) -> (List.fold_left (fun acc curr -> acc ^ "\n" ^ (main_generate consts fvars depth curr) ^ "\n") "" lst)
  | Var'(VarFree(v)) -> "mov rax, qword [fvar_tbl + 8*"^(string_of_int (getIndex_fvars fvars v))^"]\n"
  | Set'(Var'(VarFree(s)), e') -> (main_generate consts fvars depth e') ^
                                   "mov qword [fvar_tbl+8*"^(string_of_int ((getIndex_fvars fvars s)))^"], rax\nmov rax, SOB_VOID_ADDRESS\n"
  | Var'(VarParam(_, minor)) -> "mov qword rax, [rbp + "^(string_of_int (8*(minor+4)))^"]\n"
  | Set'(Var'(VarParam(_, minor)), e') ->
        (main_generate consts fvars depth e') ^ "\nmov qword [rbp + "^(string_of_int (8*(4+minor)))^"], rax\nmov rax, SOB_VOID_ADDRESS\n"
  | Var'(VarBound(_, major, minor)) ->
      "mov rax, qword [rbp + 16]\n"^
      "mov rax, qword [rax + "^(string_of_int (major*8))^"]\n"^
      "mov rax, qword [rax + "^(string_of_int (minor*8))^"]\n"
  | Box'(var) -> (main_generate consts fvars depth (Var'(var))) ^ (*now rax holds the value of var*)
                  "MALLOC r11, 8\n" ^ (*allocating memory for the box pointer in r11*)
                  "mov qword [r11], rax\n" ^
                  "mov rax, r11\n" (*now rax points to the location of the value of var*)
  | Set'(Var'(VarBound(_, major, minor)), e') ->
        ((main_generate consts fvars depth e') ^
        "mov rbx, qword [rbp + 8 ∗ 2]\n" ^
        "mov rbx, qword [rbx + 8 ∗"^(string_of_int major)^"]\n"^
        "mov qword [rbx + 8 ∗"^(string_of_int minor)^"], rax\n"^
        "mov rax, SOB_VOID_ADDRESS\n")
  | Def'(def_var, def_val) -> (match def_var with
                               | Var'(VarFree(v)) -> ((main_generate consts fvars depth def_val) ^ (*now rax holds the value of def_val*)
                                                      "\nmov [fvar_tbl + 8*"^(string_of_int (getIndex_fvars fvars v))^"], rax\nmov rax, SOB_VOID_ADDRESS")
                               | _ -> ((main_generate consts fvars depth def_var) ^ "\nmov rdi, rax\n" ^
                                       (main_generate consts fvars depth def_val) ^ "\n mov [rdi], rax\nmov rax, SOB_VOID_ADDRESS"))
  | Or'(lst) -> (or_helper consts fvars lst (random_str_num 5) depth)
  | If'(test, dit, dif) -> (if_helper consts fvars test dit dif depth)
  | BoxGet' (v) -> (main_generate consts fvars depth (Var'(v)))  ^ "\n" ^
                      "mov rax, qword [rax]\n"
  | BoxSet' (v, e') -> (main_generate consts fvars depth e') ^ "\n" ^
                          "push rax\n" ^
                          (main_generate consts fvars depth (Var'(v))) ^ "\n" ^
                          "pop qword [rax]\n" ^ 
                          "mov rax, SOB_VOID_ADDRESS\n"
  | LambdaSimple'(params, body) -> (if depth = 0
                                    then (top_level_lambda_helper consts fvars depth body)
                                    else (nested_lambda_helper consts fvars depth body))
  | LambdaOpt'(params, opt_param, body) -> (if depth = 0
                                            then (top_level_lambda_opt_helper consts fvars depth body (List.length params))
                                            else (nested_lambda_opt_helper consts fvars depth body (List.length params)))
  | Applic'(operator, args) -> (applic_helper consts fvars depth operator args)
  | ApplicTP'(operator, args) -> (applic_tp_helper consts fvars depth operator args)
  | _ -> ";THIS IS A MISTAKE";

  and if_helper consts fvars test dit dif depth =
    let else_label = "Lelse_" ^ (random_str_num 5) in
    let exit_label = "Lexit_" ^ (random_str_num 5) in
    (main_generate consts fvars depth test) ^ "\n" ^
    "cmp rax, SOB_FALSE_ADDRESS\n" ^
    "je " ^ (else_label) ^ "\n" ^
    (main_generate consts fvars depth dit) ^ "\n" ^
    "jmp " ^ (exit_label) ^ "\n" ^
    (else_label) ^ ":\n" ^
    (main_generate consts fvars depth dif) ^ "\n" ^
    (exit_label) ^ ":\n";
  

  and or_helper consts fvars lst str_ind depth =
    match lst with
    | [] -> "\nLexit_" ^ (str_ind)^ ":\n"
    | expr :: [] ->  (main_generate consts fvars depth expr) ^ (or_helper consts fvars [] str_ind depth)
    | expr :: rest -> ((main_generate consts fvars depth expr) ^ "\ncmp rax, SOB_FALSE_ADDRESS\njne Lexit_" ^ (str_ind)
                      ^ "\n" ^ (or_helper consts fvars rest str_ind depth));

  and nested_lambda_opt_helper consts fvars depth body num_of_non_opt_params = 
    let str_num = (random_str_num 5) in
    let start_label = "Lcode_" ^ (str_num) in
    let end_label = "Lcont_" ^ (str_num) in
    let str_num_non_opt_params = string_of_int(num_of_non_opt_params) in
    let lcode =
      "mov rbp, r14\n" ^
      "push rbp\n" ^
      "mov rbp, rsp\n" ^
      (main_generate consts fvars (depth+1) body) ^
      "mov rbx, [rsp + 8]\n" ^
      "\nleave\n" ^ 
      "ret\n" ^ 
      end_label ^ ":\n" in
    let ext_env =
      "\nmov rsi, [rbp + 8 * 3]\t\t\t;; (*rsi holds the number of parametres on the stack*)\n" ^
      "inc rsi\n" ^ (*incrementing to include magic*)
      "lea rsi, [rsi * 8]\n" ^ (*rsi holds the number of bytes to allocate for the new vector which is number_of_params + 1 (for magic)*)
      "MALLOC rdx, rsi\t\t\t;; (*now rdx points to the allocated memory for the new vector*)\n" ^  
      "mov rcx, [rbp + 8 * 3]\n" ^ (*rcx holds the number of parameters*)
      (*"inc rcx\t\t\t;;(*rcx holds the number of parametres on the stack + 1 (for magic),  rcx is the loop counter*)\n" ^ *)
      "mov rdi, 0\t\t\t;;(*rdi will be used to point to the next address in the vector*)\n" ^ 
      "\nmov r9, 4\n" ^
      ";; (*start of loop to copy parameters to the new allocated vector*)\n" ^
      "copy_params_loop_" ^ (str_num) ^ ":\n" ^
      "cmp rdi, rcx\n" ^ 
      "je after_params_copy_" ^ (str_num) ^ "\n" ^
      "mov rsi, [rbp + 8 * r9]\t\t\t;;(*now rsi points to the next parameter on the stack*)\n" ^ 
      "mov [rdx + 8*rdi], rsi\t\t\t;;(*copying the parameter to the new allocated vector*)\n" ^ 
      "inc rdi\n" ^
      "inc r9\n" ^
      "jmp copy_params_loop_" ^ (str_num) ^ "\n" ^ (*End of loop*)
      ";; (*now rdx points to the new vector to be added to ext_env*)\n" ^
      ";; (*mov 0 to all neccessary registers*)\n" ^
      "after_params_copy_" ^ (str_num) ^ ":\n" ^
      "mov qword [rdx + 8*rdi], SOB_NIL_ADDRESS\n" ^
      "mov rcx, 0\nmov rdi, 0\nmov rsi, 0\n" ^
      ";; (*now we need to create ext_env by copying env and adding the new vector*)\n" ^
      "MALLOC rbx, " ^ string_of_int((depth + 1) * 8) ^ "\t\t\t;;(*rbx points to a new allocated space for ext_env*)" ^
      "\nmov [rbx], rdx\t\t\t;;(*copying the new vector to ext_env[0]*)\n" ^ 
      "mov rsi, [rbp + 8 * 2]\t\t\t;;(*rsi points to current env*)\n" ^
      "mov rcx, " ^ string_of_int(depth) ^ "\t\t\t;;(*rcx is the loop counter*)\n" ^ 
      "mov r9, 0\t\t\t;;(*r9 will be used to point to the next vector in current env to be copied*)\n" ^ 
      "mov rdi, 1\t\t\t;;(*rdi will be used to point to the next address in ext_env*)\n" ^ 
      "mov r8, 0\n" ^
      ";; (*start of loop for copying env[i] to ext_env[i+1]*)\n" ^
      "copy_env_loop_" ^ (str_num) ^ ":\n" ^
      "cmp r9, rcx\n" ^
      "je after_env_copy_" ^ (str_num) ^ "\n" ^
      "mov r8, [rsi + 8 * r9]\t\t\t;;(*r8 points to the next vector int current env to be copied*) \n" ^
      "mov [rbx + 8 * rdi], r8\t\t\t;;(*copying the pointer to the vector from env to ext_env*)\n" ^ 
      "inc r9\n" ^
      "inc rdi\n" ^
      "jmp copy_env_loop_" ^ (str_num) ^ "\n" ^
      "after_env_copy_" ^ (str_num) ^ ":\n" in
      (*now rbx points to ext_env*) 
    let adjust_stack =
      "push rbp\n" ^
      "mov r14, rbp\n" ^
      "mov rbp, rsp\n" ^
      "mov rdi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "mov rsi, qword [rbp + 8*3]\n" ^ (*rsi holds args_count*)
      "cmp qword rdi, rsi\n" ^
      "jb vector_size_is_total_num_of_params_" ^ (str_num) ^ "\n" ^
      "mov rsi, 0\n" ^
      "mov rsi, " ^ (str_num_non_opt_params) ^ "\n" ^ (*rsi holds the number of non-optional parameters*)
      "jmp create_vector_" ^ (str_num) ^ "\n" ^
      "vector_size_is_total_num_of_params_" ^ (str_num) ^ ":\n" ^
      "mov rsi, [rbp + 8*3]\n" ^
      "create_vector_" ^ (str_num) ^ ":\n" ^
      "lea rsi, [rsi*8]\n" ^ (*rsi is the size of the vector used to save all the non-optional parameters*)
      "mov r9, 0\n" ^
      "mov rbx, 0\n" ^
      "mov rdx, 0\n" ^ (*cleaning r9, rdx and rbx*)
      "MALLOC r9, rsi\n" ^ (*now r9 points to a vector which will store all the non-optional parameters*)
      "mov rsi, 0\n" ^
      "mov rsi, " ^ (str_num_non_opt_params) ^ "\n" ^(*rsi holds the number of non-optional parameters*)
      "mov rcx, 0\n" ^ (*rcx is our loop counter*)
      "copy_non_opt_params_list_for_opt_" ^ (str_num) ^ ":\n" ^
      "cmp rcx, rsi\n" ^
      "je end_copy_non_opt_params_list_for_opt_" ^ (str_num) ^ "\n" ^
      "mov rbx, qword PVAR(rcx)\n" ^ (*rbx holds the next non-optional parameter  [rbp + 8 * rcx]*)
      "mov qword [r9 + 8 * rcx], rbx\n" ^ (*saving the parameter in the vector*)
      "inc rcx\n" ^
      "jmp copy_non_opt_params_list_for_opt_" ^ (str_num) ^ "\n" ^
      (*now r9 points to a vector containing all the non-optional parameters*)
      (*now we need to create a list of the optional parameters*)
      "end_copy_non_opt_params_list_for_opt_" ^ (str_num) ^ ":\n" ^
      "mov rsi, [rbp + 8*3]\n" ^ (*rsi holds the general number of parameters*)
      "cmp rsi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "je enlarge_stack_" ^ (str_num) ^ "\n" ^
      "shrink_stack_" ^ (str_num) ^ ":\n" ^ (*we need to save all optional params as list and push that list as one parameter*)
      "mov rdi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "dec rsi\n" ^ (*now rsi will be used to point to the last parameter which is the last optional parameter*)
      (*"dec rsi\n" ^ (*decreasing twice because of magic parameter*)*)
      "mov r12, 0\n" ^ (*cleaning, r12 will point to the list at the end of the loop*)
      "mov r11, 0\n" ^ (*cleaning*)
      "mov r10, 0\n" ^ (*cleaning*)
      "mov r11, PVAR(rsi)\n" ^ (*[rbp + 8*rsi]*)
      "dec rsi\n" ^
      "MAKE_PAIR(r12, r11, SOB_NIL_ADDRESS)\n" ^ (*now r12 points to the last pair of the optional parameters list*)
      "dec rdi\n" ^
      "create_opt_params_list_" ^ (str_num) ^ ":\n" ^
      "cmp rdi, rsi\n" ^
      "je pop_and_adjust_stack_shrink_stack_" ^ (str_num) ^ "\n" ^
      "mov r11, qword PVAR(rsi)\n" ^
      "mov r10, r12\n" ^ (*saving the cdr of the next list (which is th current list) in r10*)
      "MAKE_PAIR(r12, r11, r10)\n" ^ (*r12 points to the new list*)
      "dec rsi\n" ^
      "jmp create_opt_params_list_" ^ (str_num) ^ "\n" ^
      "pop_and_adjust_stack_shrink_stack_" ^ (str_num) ^ ":\n" ^
      "mov rsi, 0\nmov rdi, 0\nmov rcx,0\nmov rbx, 0\n" ^ (*cleaning registers*)
      "mov rdi, [rbp + 8]\n" ^ (*rdi contains the return address*)
      "mov rcx, [rbp + 8*2]\n" ^ (*rcx contains the current env*)
      "mov rsi, [rbp + 8*3]\n" ^ (*rsi holds the number of parameters*)
      "add rsp, 32\n" ^ (*poping old rbp, old ret address, curr env and old args count*)
      "mov rbx, 0\n" ^
      "lea rbx, [rsi*8]\n" ^ (*rbx holds the size of all the parametres*)
      "add rsp, rbx\n" ^ (*popping all the parameters*)
      (*now we need to push the new arguments*)
      "push qword r12\n" ^ (*pushing the optional argumants as a list*)
      (*now we need to push all the non-optional arguments*)
      (*those arguments are saved in a vector pointed by r9*)
      "mov r12, 0\n" ^ (*cleaning*)
      "mov r12, " ^ (str_num_non_opt_params) ^ "\n" ^
      "dec r12\n" ^
      "mov rbx, 0\n" ^
      "shrink_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "cmp rbx, r12\n" ^
      "jbe end_shrink_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "push qword [r9 + 8*r12]\n" ^
      "dec r12\n" ^
      "jmp shrink_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "end_shrink_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "mov r15, 0\n" ^
      "dec r15\n" ^
      "cmp r15, r12\n" ^
      "je dont_push_" ^ (str_num) ^ "\n" ^
      "push qword [r9 + 8*r12]\n" ^
      "dont_push_" ^ (str_num) ^ ":\n" ^
      (*now we need to push new args_count which is the number of non_optional + 1 for the optional list*)
      "mov rsi, 0\n" ^ (*cleaning*)
      "mov rsi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "inc rsi\n" ^
      "push rsi\n" ^ (*pushing the new args_count*)
      "push rcx\n" ^ (*pushing the env*)
      "push rdi\n" ^ (*pushing return address*)
      "jmp body_of_opt_" ^ (str_num) ^ "\n" ^
      (*end of shrink stack*)


      (*start of enlarge stack*)
      "enlarge_stack_" ^ (str_num) ^ ":\n" ^
      
      (*r9 already points to a vector containig all the non-optional parameters*)
      (*we just need to pop the stack and push all the parameters plus the empty list*)
      "mov rsi, 0\nmov rdi, 0\nmov rcx,0\nmov rbx, 0\nmov rdx, 0\n" ^ (*cleaning registers*)
      "mov rdx, qword [rbp + 8*3]\n" ^ (*rdx also contains the args_count*)
      "mov rdi, [rbp + 8]\n" ^ (*rdi contains the return address*)
      "mov rcx, [rbp + 8*2]\n" ^ (*rcx contains the current env*)
      "mov rsi, [rbp + 8*3]\n" ^ (*rsi holds the number of parameters*)
      "add rsp, 32\n" ^ (*poping old rbp, old ret address, curr env and old args count*)
      "lea rbx, [rsi*8]\n" ^ (*rbx holds the size of all the parametres*)
      "add rsp, rbx\n" ^ (*popping all the parameters*)
      "push SOB_NIL_ADDRESS\n" ^ (*pushing the empty list as the last argument*)
      "mov r10, 0\nmov r11, 0\n" ^ (*cleaning*)
      "mov r10, rsi\n" ^ (*(str_num_non_opt_params) ^ "\n" ^*)
      "dec r10\n" ^ (*r10 holds the args_count - 1, it will be used to copy the arguments from the vector pointed by r9*)
      "mov rbx, 0\n" ^
      "dec rbx\n" ^
      "enlarge_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "cmp rbx, r10\n" ^
      "je end_enlarge_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "push qword [r9 + 8*r10]\n" ^
      "dec r10\n" ^
      "jmp enlarge_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "end_enlarge_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "mov rsi, rdx\n" ^ (*[rbp + 8*3]*) (*rsi holds arg_count*)
      "inc rsi\n" ^ (*now rsi holds the new parameter count*)
      "push rsi\n" ^ (*pushing the argument count*)
      "push rcx\n" ^ (*pushing the current env*)
      "push rdi\n" ^ (*pushing the return address*)
      (*"push rbp\n" ^*)
      "body_of_opt_" ^ (str_num) ^ ":\n" in
    ext_env ^ "\n" ^
    "MAKE_CLOSURE(rax, rbx, " ^ start_label ^ ")\n" ^
    "jmp " ^ end_label ^ "\n" ^
    start_label ^ ":\n" ^
    adjust_stack ^
    lcode ^ "\n";

  
  and top_level_lambda_opt_helper consts fvars depth body num_of_non_opt_params = 
    let str_num = (random_str_num 5) in
    let start_label = "Lcode_" ^ (str_num) in
    let end_label = "Lcont_" ^ (str_num) in
    let str_num_non_opt_params = string_of_int(num_of_non_opt_params) in
    let lcode =
      "mov rbp, r14\n" ^
      "push rbp\n" ^
      "mov rbp, rsp\n" ^
      (main_generate consts fvars (depth+1) body) ^
      "\nleave\n" ^ 
      "ret\n" ^ 
      end_label ^ ":\n" in
    let adjust_stack =
      "push rbp\n" ^
      "mov r14, rbp\n" ^
      "mov rbp, rsp\n" ^
      "mov rdi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "mov rsi, qword [rbp + 8*3]\n" ^ (*rsi holds args_count*)
      "cmp qword rdi, rsi\n" ^
      "jb vector_size_is_total_num_of_params_" ^ (str_num) ^ "\n" ^
      "mov rsi, 0\n" ^
      "mov rsi, " ^ (str_num_non_opt_params) ^ "\n" ^ (*rsi holds the number of non-optional parameters*)
      "jmp create_vector_" ^ (str_num) ^ "\n" ^
      "vector_size_is_total_num_of_params_" ^ (str_num) ^ ":\n" ^
      "mov rsi, [rbp + 8*3]\n" ^
      "create_vector_" ^ (str_num) ^ ":\n" ^
      "lea rsi, [rsi*8]\n" ^ (*rsi is the size of the vector used to save all the non-optional parameters*)
      "mov r9, 0\n" ^
      "mov rbx, 0\n" ^
      "mov rdx, 0\n" ^ (*cleaning r9, rdx and rbx*)
      "MALLOC r9, rsi\n" ^ (*now r9 points to a vector which will store all the non-optional parameters*)
      "mov rsi, 0\n" ^
      "mov rsi, " ^ (str_num_non_opt_params) ^ "\n" ^(*rsi holds the number of non-optional parameters*)
      "mov rcx, 0\n" ^ (*rcx is our loop counter*)
      "copy_non_opt_params_list_for_opt_" ^ (str_num) ^ ":\n" ^
      "cmp rcx, rsi\n" ^
      "je end_copy_non_opt_params_list_for_opt_" ^ (str_num) ^ "\n" ^
      "mov rbx, qword PVAR(rcx)\n" ^ (*rbx holds the next non-optional parameter  [rbp + 8 * rcx]*)
      "mov qword [r9 + 8 * rcx], rbx\n" ^ (*saving the parameter in the vector*)
      "inc rcx\n" ^
      "jmp copy_non_opt_params_list_for_opt_" ^ (str_num) ^ "\n" ^
      (*now r9 points to a vector containing all the non-optional parameters*)
      (*now we need to create a list of the optional parameters*)
      "end_copy_non_opt_params_list_for_opt_" ^ (str_num) ^ ":\n" ^
      "mov rsi, [rbp + 8*3]\n" ^ (*rsi holds the general number of parameters*)
      "cmp rsi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "je enlarge_stack_" ^ (str_num) ^ "\n" ^
      "shrink_stack_" ^ (str_num) ^ ":\n" ^ (*we need to save all optional params as list and push that list as one parameter*)
      "mov rdi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "dec rsi\n" ^ (*now rsi will be used to point to the last parameter which is the last optional parameter*)
      (*"dec rsi\n" ^ (*decreasing twice because of magic parameter*)*)
      "mov r12, 0\n" ^ (*cleaning, r12 will point to the list at the end of the loop*)
      "mov r11, 0\n" ^ (*cleaning*)
      "mov r10, 0\n" ^ (*cleaning*)
      "mov r11, PVAR(rsi)\n" ^ (*[rbp + 8*rsi]*)
      "dec rsi\n" ^
      "MAKE_PAIR(r12, r11, SOB_NIL_ADDRESS)\n" ^ (*now r12 points to the last pair of the optional parameters list*)
      "dec rdi\n" ^
      "create_opt_params_list_" ^ (str_num) ^ ":\n" ^
      "cmp rdi, rsi\n" ^
      "je pop_and_adjust_stack_shrink_stack_" ^ (str_num) ^ "\n" ^
      "mov r11, qword PVAR(rsi)\n" ^
      "mov r10, r12\n" ^ (*saving the cdr of the next list (which is th current list) in r10*)
      "MAKE_PAIR(r12, r11, r10)\n" ^ (*r12 points to the new list*)
      "dec rsi\n" ^
      "jmp create_opt_params_list_" ^ (str_num) ^ "\n" ^
      "pop_and_adjust_stack_shrink_stack_" ^ (str_num) ^ ":\n" ^
      "mov rsi, 0\nmov rdi, 0\nmov rcx,0\nmov rbx, 0\n" ^ (*cleaning registers*)
      "mov rdi, [rbp + 8]\n" ^ (*rdi contains the return address*)
      "mov rcx, [rbp + 8*2]\n" ^ (*rcx contains the current env*)
      "mov rsi, [rbp + 8*3]\n" ^ (*rsi holds the number of parameters*)
      "add rsp, 32\n" ^ (*poping old rbp, old ret address, curr env and old args count*)
      "mov rbx, 0\n" ^
      "lea rbx, [rsi*8]\n" ^ (*rbx holds the size of all the parametres*)
      "add rsp, rbx\n" ^ (*popping all the parameters*)
      (*now we need to push the new arguments*)
      "push qword r12\n" ^ (*pushing the optional argumants as a list*)
      (*now we need to push all the non-optional arguments*)
      (*those arguments are saved in a vector pointed by r9*)
      "mov r12, 0\n" ^ (*cleaning*)
      "mov r12, " ^ (str_num_non_opt_params) ^ "\n" ^
      "dec r12\n" ^
      "mov rbx, 0\n" ^
      "shrink_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "cmp rbx, r12\n" ^
      "jbe end_shrink_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "push qword [r9 + 8*r12]\n" ^
      "dec r12\n" ^
      "jmp shrink_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "end_shrink_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "mov r15, 0\n" ^
      "dec r15\n" ^
      "cmp r15, r12\n" ^
      "je dont_push_" ^ (str_num) ^ "\n" ^
      "push qword [r9 + 8*r12]\n" ^
      "dont_push_" ^ (str_num) ^ ":\n" ^
      (*now we need to push new args_count which is the number of non_optional + 1 for the optional list*)
      "mov rsi, 0\n" ^ (*cleaning*)
      "mov rsi, " ^ (str_num_non_opt_params) ^ "\n" ^
      "inc rsi\n" ^
      "push rsi\n" ^ (*pushing the new args_count*)
      "push rcx\n" ^ (*pushing the env*)
      "push rdi\n" ^ (*pushing return address*)
      "jmp body_of_opt_" ^ (str_num) ^ "\n" ^
      (*end of shrink stack*)


      (*start of enlarge stack*)
      "enlarge_stack_" ^ (str_num) ^ ":\n" ^
      (*r9 already points to a vector containig all the non-optional parameters*)
      (*we just need to pop the stack and push all the parameters plus the empty list*)
      "mov rsi, 0\nmov rdi, 0\nmov rcx,0\nmov rbx, 0\nmov rdx, 0\n" ^ (*cleaning registers*)
      "mov rdx, qword [rbp + 8*3]\n" ^ (*rdx also contains the args_count*)
      "mov rdi, [rbp + 8]\n" ^ (*rdi contains the return address*)
      "mov rcx, [rbp + 8*2]\n" ^ (*rcx contains the current env*)
      "mov rsi, [rbp + 8*3]\n" ^ (*rsi holds the number of parameters*)
      "add rsp, 32\n" ^ (*poping old rbp, old ret address, curr env and old args count*)
      "lea rbx, [rsi*8]\n" ^ (*rbx holds the size of all the parametres*)
      "add rsp, rbx\n" ^ (*popping all the parameters*)
      "push SOB_NIL_ADDRESS\n" ^ (*pushing the empty list as the last argument*)
      "mov r10, 0\nmov r11, 0\n" ^ (*cleaning*)
      "mov r10, rsi\n" ^ (*(str_num_non_opt_params) ^ "\n" ^*)
      "dec r10\n" ^ (*r10 holds the args_count - 1, it will be used to copy the arguments from the vector pointed by r9*)
      "mov rbx, 0\n" ^
      "dec rbx\n" ^
      "enlarge_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "cmp rbx, r10\n" ^
      "je end_enlarge_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "push qword [r9 + 8*r10]\n" ^
      "dec r10\n" ^
      "jmp enlarge_push_non_optional_params_loop_" ^ (str_num) ^ "\n" ^
      "end_enlarge_push_non_optional_params_loop_" ^ (str_num) ^ ":\n" ^
      "mov rsi, rdx\n" ^ (*[rbp + 8*3]*) (*rsi holds arg_count*)
      "inc rsi\n" ^ (*now rsi holds the new parameter count*)
      "push rsi\n" ^ (*pushing the argument count*)
      "push rcx\n" ^ (*pushing the current env*)
      "push rdi\n" ^ (*pushing the return address*)
      (*"push rbp\n" ^*)
      "body_of_opt_" ^ (str_num) ^ ":\n" in
    "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ start_label ^ ")\n" ^
    "jmp " ^ end_label ^ "\n" ^
    start_label ^ ":\n" ^
    adjust_stack ^
    lcode ^ "\n";


  and top_level_lambda_helper consts fvars depth body =
    let str_num = (random_str_num 5) in
    let start_label = "Lcode_" ^ (str_num) in
    let end_label = "Lcont_" ^ (str_num) in
    let lcode =
      start_label ^ ":\n" ^
      "push rbp\n" ^ 
      "mov rbp, rsp\n" ^ 
      (main_generate consts fvars (depth+1) body) ^ 
      "\nleave\n" ^ 
      "ret\n" ^ 
      end_label ^ ":\n" in
    "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ start_label ^")\n" ^
    "jmp " ^ end_label ^ "\n" ^
    lcode ^ "\n";
   
  and nested_lambda_helper consts fvars depth body =
    let str_num = (random_str_num 5) in
    let start_label = "Lcode_" ^ (str_num) in
    let end_label = "Lcont_" ^ (str_num) in
    let lcode =
      start_label ^ ":\n" ^
      "push rbp\n" ^
      "mov rbp, rsp\n" ^
      (main_generate consts fvars (depth+1) body) ^
      "\nleave\n" ^
      "ret\n" ^
      end_label ^ ":\n" in 
    let ext_env =
      "\nmov rsi, [rbp + 8 * 3]\t\t\t;; (*rsi holds the number of parametres on the stack*)\n" ^ 
      "inc rsi\n" ^ (*incrementing for magic*)
      "lea rsi, [rsi * 8]\n" ^ (*rsi holds the number of bytes to allocate for the new vector which is number_of_params + 1 (for magic)*)
      "MALLOC rdx, rsi\t\t\t;; (*now rdx points to the allocated memory for the new vector*)\n" ^  
      "mov rcx, [rbp + 8 * 3]\n" ^ (*rcx holds the number of parameters*)
      (*"inc rcx\t\t\t;;(*rcx holds the number of parametres on the stack + 1 (for magic),  rcx is the loop counter*)\n" ^ *)
      "mov rdi, 0\t\t\t;;(*rdi will be used to point to the next address in the vector*)\n" ^ 
      "\nmov r9, 4\n" ^
      ";; (*start of loop to copy parameters to the new allocated vector*)\n" ^
      "copy_params_loop_" ^ (str_num) ^ ":\n" ^
      "cmp rdi, rcx\n" ^ 
      "je after_params_copy_" ^ (str_num) ^ "\n" ^
      "mov rsi, [rbp + 8 * r9]\t\t\t;;(*now rsi points to the next parameter on the stack*)\n" ^ 
      "mov [rdx + 8*rdi], rsi\t\t\t;;(*copying the parameter to the new allocated vector*)\n" ^ 
      "inc rdi\n" ^
      "inc r9\n" ^
      "jmp copy_params_loop_" ^ (str_num) ^ "\n" ^ (*End of loop*)
      ";; (*now rdx points to the new vector to be added to ext_env*)\n" ^
      ";; (*mov 0 to all neccessary registers*)\n" ^
      "after_params_copy_" ^ (str_num) ^ ":\n" ^
      "mov qword [rdx + 8*rdi], SOB_NIL_ADDRESS\n" ^ (*adding magic to the end of the new vector*)
      "mov rcx, 0\nmov rdi, 0\nmov rsi, 0\n" ^
      ";; (*now we need to create ext_env by copying env and adding the new vector*)\n" ^
      "MALLOC rbx, " ^ string_of_int((depth + 1) * 8) ^ "\t\t\t;;(*rbx points to a new allocated space for ext_env*)" ^
      "\nmov [rbx], rdx\t\t\t;;(*coping the new vector to ext_env[0]*)\n" ^ 
      "mov rsi, [rbp + 8 * 2]\t\t\t;;(*rsi points to current env*)\n" ^ 
      "mov rcx, " ^ string_of_int(depth) ^ "\t\t\t;;(*rcx is the loop counter*)\n" ^ 
      "mov r9, 0\t\t\t;;(*r9 will be used to point to the next vector in current env to be copied*)\n" ^ 
      "mov rdi, 1\t\t\t;;(*rdi will be used to point to the next address in ext_env*)\n" ^ 
      "mov r8, 0\n" ^
      ";; (*start of loop for copying env[i] to ext_env[i+1]*)\n" ^
      "copy_env_loop_" ^ (str_num) ^ ":\n" ^
      "cmp r9, rcx\n" ^
      "je after_env_copy_" ^ (str_num) ^ "\n" ^
      "mov r8, [rsi + 8 * r9]\t\t\t;;(*r8 points to the next vector int current env to be copied*) \n" ^ 
      "mov [rbx + 8 * rdi], r8\t\t\t;;(*copying the pointer to the vector from env to ext_env*)\n" ^ 
      "inc r9\n" ^
      "inc rdi\n" ^
      "jmp copy_env_loop_" ^ (str_num) ^ "\n" ^
      "after_env_copy_" ^ (str_num) ^ ":\n" in
      (*now rbx points to ext_env*) 
    ext_env ^ "\n" ^ 
    "MAKE_CLOSURE(rax, rbx, " ^ start_label ^ ")\n" ^
    "jmp " ^ end_label ^ "\n" ^
    lcode ^ "\n";
  
  
  and applic_tp_helper consts fvars depth operator args =
    let str_num = (random_str_num 5) in
    let rec args_str revresed_args str = (*reversed because the arguments are pushed in reversed order*)
      match revresed_args with
      | arg :: rest -> (let next_str = str ^ "\n" ^
                                       (main_generate consts fvars depth arg) ^ "\n" ^
                                       "push rax\n" in
                        args_str rest next_str)
      | [] -> str in
    let push_arguments = args_str (List.rev args) "\npush SOB_NIL_ADDRESS\n" in
    let operator_str = main_generate consts fvars depth operator in
    "mov r13, qword [rbp + 8]\n" ^ (*save old return address in r13*)
    (*now we need to fix the stack*)
    push_arguments ^ "\n" ^
    "push " ^ string_of_int((List.length args)) ^ "\n" ^
    operator_str ^
    (*now rax points to the closure*)
    "push qword [rax + 1]\n" ^ (*pushing the env*)
    "push qword [rbp + 8]\n" ^ (*pushing old return address*)
    (*now rsp points to new args_count and rbp point to the old frame*)
    "mov rsi, [rbp + 8 * 3]\n" ^ (*rsi holds old args_count*)
    "shl rsi, 3\n" ^ 
    (*we need to calculate the start address of the old frame on the stack*)
    "mov rbx, 0\n" ^ (*cleaning*)
    "mov rbx, rbp\n" ^ (*rbx will be used to calculate the start of the old frame*)
    "add rbx, 32\n" ^ (*adding the sizes of old rbp, env, return address and args_count*)
    "add rbx, rsi\n" ^ (*adding the size of all the arguments*)
    (*now rbx points to the address from where we need to start overwriting the old frame*)
    (*first let's move all the new arguments to the old frame address*)
    (*we need to calculate the size of the new frame*)
    "mov rdx, [rsp + 16]\n" ^ (*new args count in rdx*)
    "my_stop:\n" ^
    (*"dec rdx\n" ^ (*this is becuse we don't want to copy magic because it already exist in the old frame*)*)
    "shl rdx, 3\n" ^
    "mov rcx, 0\n" ^ (*cleaning*)
    "mov rcx, rsp\n" ^ (*rcx will be used to point to the next qword to move to the old frame address*)
    "add rcx, 24\n" ^ (*adding 24 for env, old return address and args_count*)
    "add rcx, rdx\n" ^ (*adding the size of all arguments*)
    (*rbx points to the start of the old frame (the last argument of the old frame)
      rcx points to the start of the new one (the last argument of the frame)*)
    "mov r9, 0\nmov r10, 0\n" ^ (*cleaning*)
    "mov r9, [rsp + 16]\n" ^ 
    (*"dec r9\n" ^ (*this is becuse we don't want to copy magic because it already exist in the old frame*)*)
    "add r9, 3\n" ^ (*r9 will be our loop counter where we copy the new frame to the old frame address*)
    (*adding 3 for ret_address, env and args count*)
    "move_move_frame_loop_" ^ (str_num) ^ ":\n" ^
    "cmp r9, 0\n" ^
    "je end_of_frame_loop_" ^ (str_num) ^ "\n" ^
    "mov r10, qword [rcx]\n" ^
    "mov qword [rbx], r10\n" ^
    "sub rcx, 8\nsub rbx,8\n" ^ 
    "dec r9\n" ^
    "jmp move_move_frame_loop_" ^ (str_num) ^ "\n" ^
    "end_of_frame_loop_" ^ (str_num) ^ ":\n" ^
    (*now rbx point points to the base address of the new frame after it was copied*)
    "mov r10, qword [rcx]\n" ^
    "mov qword [rbx], r10\n" ^
    (*"add rbp, 8\n" ^*)
    (*"mov rdi, [rbp]\n" ^
    "mov r8, [rbp + 8]\n" ^
    "mov r9, [rbp + 8*2]\n" ^
    "mov r10, [rbp + 8*3]\n" ^
    "mov r10, [r10 + 1]\n" ^
    "mov r11, [rbp + 8*4]\n" ^
    "mov r11, [r11 + 1]\n" ^
    "mov r12, [rbp + 8*5]\n" ^
    "mov r12, [r12 + 1]\n" ^
    "mov r13, [rbp + 8*6]\n" ^
    "mov rdx, SOB_NIL_ADDRESS\n" ^*)
    "jmp [rax + 9]\n"; (*jumping to function code*)



  
  
  and applic_helper consts fvars depth operator args =
    let str_num = (random_str_num 5) in
    let rec args_str revresed_args str = (*reversed because the arguments are pushed in reversed order*)
      match revresed_args with
      | arg :: rest -> (let next_str = str ^ "\n" ^
                                       (main_generate consts fvars depth arg) ^ "\n" ^
                                       "push rax\n" in
                        args_str rest next_str)
      | [] -> str in
    let push_arguments = args_str (List.rev args) "\npush SOB_NIL_ADDRESS\n" in
    (*let operator_str = main_generate consts fvars depth operator in*)
    push_arguments ^ "\n" ^
    "push " ^ string_of_int((List.length args)) ^ "\n" ^
    (main_generate consts fvars depth operator) ^ "\n" ^
    "push qword [rax + 1]\t\t\t;;(*pushing env on the stack*)\n" ^
    "call [rax + 9]\n" ^
    "add rsp, 8\t\t\t;;(*popping the environment pointer*)\n" ^ 
    "pop rbx\t\t\t;;(*popping and saving the argument counter in rbx*)\n" ^
    "shl rbx, 3\t\t\t;;(*now rbx holds the sum of sizes of all the arguments to pop*)\n" ^ 
    "add rsp, rbx\t\t\t;;(*popping all the arguments*)\n" ^
    "add rsp, 8\n" ^ (*popping magic*)
    "after_applic_" ^ (str_num) ^ ":\n";;

  

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = 
    let sexps_list = get_all_sexp_multiple_asts (rename_tags_all_asts asts 0) in
    let tagged_tuples_list = collect_all_tagged_sexps sexps_list in
    let expanded_sexps_list = remove_dups_from_left (expand_list sexps_list) in
    from_sexp_lst_to_const_tbl tagged_tuples_list expanded_sexps_list;;
  let make_fvars_tbl asts = create_free_vars_table asts;;
  let generate consts fvars e =
    main_generate consts fvars 0 e
end;;

