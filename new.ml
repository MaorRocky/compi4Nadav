let rec add_fvar_tuple fvars_to_add fvar_table index =
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
  let fvars_from_ast = remove_dups_from_left (get_all_fvars_multiple_asts asts) in
  (add_fvar_tuple fvars_from_ast initial_fvars 34);;*)

(* find index of free var in fvars_table *)


let rec getIndex_fvars fvars_table fvar_name =
  if List.length fvars_table < 1 
  then -1
  else
    let (name,fvar_index) = (List.hd fvars_table) in
    if(String.equal name fvar_name) 
    then fvar_index
    else getIndex_fvars (List.tl fvars_table) fvar_name ;;


let getOffset_const_table const const_table =
  let (sexp, (offset, str)) =
    (List.find (fun (sexp, (address,str)) -> sexpr_eq sexp const) const_table) in
  offset;;

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
    "je .Lelse_" ^ (string_of_int ind) ^ "\n" ^  
    (mainGenerate dit env) ^ "\n" ^
    "jmp .Lexit_" ^ (string_of_int ind) ^ "\n" ^
    ".Lelse_" ^ (string_of_int ind) ^ ":\n" ^
    (mainGenerate dif env) ^ "\n" ^
    ".Lexit_" ^ (string_of_int ind) ^ ":\n"

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
      | Const'(Sexpr(c)) -> let i = (getOffset_const_table c consts) in "mov rax, const_tbl+"^(string_of_int i)^"\n"
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
      |Var'(VarFree(v)) -> "mov rax, qword [fvar_tbl + 8*"^(string_of_int ((getIndex_fvars fvars v)))^"]\n"
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