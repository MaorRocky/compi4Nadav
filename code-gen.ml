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
  (*| TaggedSexpr(name, sexpr) -> [Pair(name)]*)
  | Pair(a, b) -> List.append (List.append (expand_sexp a) (expand_sexp b)) [sexp]
  | _ -> [sexp];;

let rec expand_list lst = 
  if List.length lst = 0
  then lst
  else List.append (expand_sexp (List.hd lst)) (expand_list (List.tl lst))

let rec from_sexp_lst_to_const_tbl lst =
  let global_lst = ref [(Void, (0, "MAKE_VOID")); (Sexpr(Nil), (1, "MAKE_NIL"));
                        (Sexpr(Bool(false)), (2, "MAKE_BOOL(0)")); (Sexpr(Bool(true)), (4, "MAKE_BOOL(1)"))] in
  let add_next_tuple sexp =
    let rec get_offset_of_sexp sexp const_tbl = 
        match const_tbl with
        | (Sexpr(sexpr), (offset, representation)) :: rest when (sexpr_eq sexpr sexp) -> offset
        | tuple :: rest -> get_offset_of_sexp sexp rest
        | [] -> (-1) in
    let get_next_offset = 
        let last_tuple = List.nth !global_lst ((List.length !global_lst) - 1) in
        match last_tuple with
        | (Sexpr(Bool(_)), (offset, representation)) -> offset + 2
        | (Sexpr(Char(_)), (offset, representation)) -> offset + 2
        | (Sexpr(Number(_)), (offset, representation)) -> offset + 9
        | (Sexpr(String(str)), (offset, representation)) -> offset + 9 + (String.length str)
        | (Sexpr(Symbol(str)), (offset, representation)) -> offset + 9
        | (Sexpr(Pair(car, cdr)), (offset, representation)) -> offset + 17 in
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
    | Pair(car, cdr) -> (let car_offset = string_of_int(get_offset_of_sexp car !global_lst) in
                                let cdr_offset = string_of_int(get_offset_of_sexp cdr !global_lst) in
                                global_lst := List.append !global_lst 
                                            [(Sexpr(sexp), (offset, "MAKE_LITERAL_PAIR(consts+"^car_offset^", consts+"^cdr_offset^")"))]) in
  let dont_care = List.map add_next_tuple lst in
  car !global_lst dont_care;;

let my_func = fun str -> from_sexp_lst_to_const_tbl (remove_dups_from_left (expand_list (remove_dups_from_left (get_all_sexps (my_run (my_tag (my_read_sexpr str)))))))

let check_tags = fun str -> rename_tags_all_asts (my_runs (my_tags (my_read_sexprs str)))

(* get_all_sexps (boxing (tail_cals false (lexical_addresses [] [] false ()))) *)


(*let rec get_all_freeVars expr'=
  let global_lst = ref [] in
  let rec func expr' = 
    match expr' with
    | Const' (Sexpr(a))-> []
    | Var'(VarFree(var)) -> [var]
    | Box'(var) -> ()
    (* | BoxGet'(var) -> () *)
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
  let initial_fvars =["boolean?",(0, "boolean?"); "float?",(1,"float?"); "integer?",(2,"integer?");
  "pair?",(3,"pair?");
  "null?",(4,"null?"); "char?",(5,"char?"); "vector?",(6,"vector?"); "string?",(7,"string?");
  "procedure?",(8,"procedure?"); "symbol?", (9,"symbol?"); "string-length", (10, "string-length") ;
  "string-ref",(11, "string-ref") ; "string-set!",(12, "string-set!"); "make-string",(13,"make-string");
  "vector-length", (14, "vector-length"); "vector-ref",(15,"vector-ref"); "vector-set!",(16,"vector-set!");
  "make-vector", (17,"make-vector"); "symbol->string",(18,"symbol->string");
  "char->integer", (19, "char->integer"); "integer->char", (20,"integer->char"); "eq?", (21, "eq?");
  "+",(22,"+"); "*",(23,"*"); "-",(24,"-"); "/",(25,"/"); "<", (26,"<" ); "=",(27,"=");
  "car", (28,"car"); "cdr",(29,"cdr");"set-car!",(30,"set-car!");"set-cdr!",(31,"set-cdr!");
  "apply", (32, "apply");"cons",(33,"cons");
(*  "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"*)] in
  asts
  ;; *)

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

