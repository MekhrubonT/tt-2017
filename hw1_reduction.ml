open Hw1

module SET = Set.Make(String);;
module MAP = Map.Make(String);;

let equal a b = (a = b);;

let rec free_vars_impl bounded tree = match tree with 
	Var a -> if SET.mem a bounded then [] else a::[]
	| Abs (var, lambda) -> free_vars_impl (SET.add var bounded) lambda
	| App (lhs, rhs) -> List.append (free_vars_impl bounded lhs) (free_vars_impl bounded rhs);;

let rec free_vars tree = free_vars_impl SET.empty tree;;
	

let rec free_to_subst_impl blc_vars tree varname = match tree with
	Var var -> true
	| Abs (var, lambda) -> if var = varname then true 
							else if (SET.mem var blc_vars) = true then false
							else free_to_subst_impl blc_vars lambda varname
	| App (lhs, rhs) -> (free_to_subst_impl blc_vars lhs varname) && (free_to_subst_impl blc_vars rhs varname);;

let free_to_subst nw tree varname = 
	let blc_vars = SET.of_list (free_vars nw) in
	free_to_subst_impl blc_vars tree varname;;

let la = lambda_of_string "a";;
let lb = lambda_of_string "b";;
let lab = lambda_of_string "a b";;
let l1 = lambda_of_string "\\a.a b";;
let l2 = lambda_of_string "\\b.a b";;
let l3 = App (Var "a", l1);;
let l4 = Abs("a", Abs("d", Abs("a", Var "c")));;

(*let rec str_list_print ls = print_string "\\\t";
						List.iter print_string ls; 
						print_string "\n";;

List.iter (fun a -> str_list_print (free_vars a)) [la; lb; lab; l1; l2; l3; l4];;*)



let rec is_normal_form x = match x with
	Var a -> true
	| Abs (var, lmb) -> is_normal_form lmb
	| App (Abs (var, lmb), rhs) -> false
	| App (lhs, rhs) -> (is_normal_form lhs) && (is_normal_form rhs);;

let print_lambda x = print_string ((string_of_lambda x)^"\n");;

let rec subst lambda oldvar nwlmb = 
	match lambda with
	Var var -> if var = oldvar then nwlmb else lambda
	| Abs (var, lmb) -> if var = oldvar then lambda else Abs(var, subst lmb oldvar nwlmb)
	| App (lhs, rhs) -> App (subst lhs oldvar nwlmb, subst rhs oldvar nwlmb);;
	

(*print_string "substtest";;
let lbab = (lambda_of_string "\\b. a b");;
print_lambda lbab;;
print_lambda (subst lbab "b" "a");;*)
	
let rec is_alpha_equivalent_impl x y cn =
	match (x, y) with
	(Var a, Var b) -> a = b
	| (Abs (lvar, llmb), Abs(rvar, rlmb)) -> is_alpha_equivalent_impl 
													(subst llmb lvar (Var ("m"^(string_of_int cn))))
													(subst rlmb rvar (Var ("m"^(string_of_int cn))))
													(cn+1)
	| App(llhs, lrhs), App(rlhs, rrhs) -> (is_alpha_equivalent_impl llhs rlhs cn ) && 
											(is_alpha_equivalent_impl lrhs rrhs cn)
	| _ -> false;;
	
let is_alpha_equivalent x y = is_alpha_equivalent_impl x y 0;;

let print_bool x = print_string (if x then "true" else "false");;

(*print_string ("l1="^(string_of_lambda l1) ^ "\n");;
print_string ("l2="^(string_of_lambda l2) ^ "\n");;
print_bool (is_alpha_equivalent l1 l2);;*)

let id = ref 0;;
let gen() = id := !id+1;
			"i"^(string_of_int !id);;

let rec rename_vars lmb map = match lmb with 
	Var var -> if MAP.mem var map then Var (MAP.find var map) else Var (gen())
	| Abs(var, rhs) -> let nn = gen() in 
						Abs (nn, rename_vars rhs (MAP.add var nn map))
	| App(lhs, rhs) -> App((rename_vars lhs map), (rename_vars rhs map));;

let rec normal_beta_reduction_impl lmb = match lmb with 
	Var a -> lmb
	| Abs (var, l) -> Abs (var, normal_beta_reduction_impl l)
	| App (Abs (var, ld), rd) -> subst ld var rd
	| App (lhs, rhs) -> if is_normal_form lhs then App (lhs, normal_beta_reduction_impl rhs)
												else App (normal_beta_reduction_impl lhs, rhs);;	

												
let normal_beta_reduction lmb = normal_beta_reduction_impl (rename_vars lmb MAP.empty);;
(*List.iter (fun x -> print_lambda x; print_lambda(rename_vars x MAP.empty)) [la; lb; lab; l1; l2; l3; l4];;*)



type lambdaRef = Varr of string | Absr of (string*(lambdaRef ref ref))
					| Appr of ((lambdaRef ref ref)*(lambdaRef ref ref));;
					
let rec lambda_to_lambdaRef tree = match tree with 
	Var a -> (Varr a)
	| Abs (var, lmb) -> Absr (var, ref (ref (lambda_to_lambdaRef lmb)))
	| App (lhs, rhs) -> Appr (ref (ref (lambda_to_lambdaRef lhs)), ref (ref (lambda_to_lambdaRef rhs)));;

let rec lambdaRef_to_lambda tree = match tree with 
	Varr a -> Var a
	| Absr (var, lmb) -> Abs(var, lambdaRef_to_lambda !(!lmb))
	| Appr (lhs, rhs) -> App(lambdaRef_to_lambda !(!lhs), lambdaRef_to_lambda !(!rhs));;
	
let rec substr tree oldvar nwlmb = match !(!tree) with
	Varr a -> if a = oldvar then tree := !nwlmb;
	| Absr (var, lmb) -> if var <> oldvar then (substr lmb oldvar nwlmb); 
	| Appr (lhs, rhs) ->  
						substr lhs oldvar nwlmb;
						substr rhs oldvar nwlmb;;

let counts = ref 0;;
						
let rec reduce_to_normal_form_impl treeRef dep = 
			
	match !(!treeRef) with 
	Varr a -> treeRef
	| Absr (var, lmb) -> 
				lmb := !(reduce_to_normal_form_impl lmb (dep + 1));
				treeRef
	| Appr ({contents = {contents = Absr (var, lhs)}}, rhs) -> 
						counts := !counts + 1;
						substr lhs var rhs;
						reduce_to_normal_form_impl treeRef (dep + 1)						
	| Appr (lhs, rhs) -> 
					lhs := !(reduce_to_normal_form_impl lhs (dep + 1));
					match !(!lhs) with 
						Absr (var, lmb) -> 
								counts := !counts + 1;
								substr lmb var rhs;
								reduce_to_normal_form_impl treeRef (dep + 1)
						| _ -> rhs := !(reduce_to_normal_form_impl rhs (dep + 1));
							treeRef;;

let reduce_to_normal_form x = 
			counts := 0;
			print_lambda x;
			let treeRef = ref (ref (lambda_to_lambdaRef (rename_vars x MAP.empty))) in
			let q = !(!(reduce_to_normal_form_impl treeRef 0)) in 
			print_string ((string_of_int !counts)^"\n");
			lambdaRef_to_lambda q;;


			

let t7 = lambda_of_string "((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))";;
print_lambda(reduce_to_normal_form t7);;
