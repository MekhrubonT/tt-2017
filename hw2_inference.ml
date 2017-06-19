open Hw1

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type


type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

module MAP = Map.Make(String);;
module SET = Set.Make(String);;


print_string "\n\n\n\nHW4\n";;

let type_counter = ref 0;;
let gen() = type_counter := !type_counter + 1;
			"m"^(string_of_int !type_counter);;

exception NotSimpleType;;

let a_elem t = Hw2_unify.Var t;;
let a_arrow l r = Hw2_unify.Fun ("arrow", [l; r]);;

let rec alg_to_simp alg = match alg with
	Hw2_unify.Var var -> S_Elem var 
	| Hw2_unify.Fun ("arrow", [l; r]) -> S_Arrow (alg_to_simp l, alg_to_simp r)
	| _ -> raise NotSimpleType;;

let rec st_to_string st = 
        match st with 
                S_Elem v -> v
                | S_Arrow (x, y) -> "(" ^ (st_to_string x) ^ " -> " ^
                (st_to_string y) ^ ")";;

let alg_to_str x = st_to_string (alg_to_simp x);;

	
let rec infer_simp_type_helper m var_types = match m with
	Var var -> ([], MAP.find var var_types)
	| Abs (var, t) -> 
					let name = (gen()) in
					let temp = MAP.add var (a_elem name) var_types in
					print_string (var^" type is "^name^"\n");
					let (ep, tp) = infer_simp_type_helper t temp in 
						(ep, a_arrow (MAP.find var temp) tp)
	| App (p, r) -> let ep, tp = infer_simp_type_helper p var_types in
					let er, tr = infer_simp_type_helper r var_types in
					let pi = a_elem (gen()) in
					print_string ("app "^(alg_to_str tp)^"\t"^(alg_to_str tr)^"\t"^(alg_to_str pi)^"\n");
					((tp, a_arrow tr pi)::(List.append ep er), pi);;

let init_free_vars_types lmb = let fv = Hw1_reduction.free_vars lmb in
							List.fold_left (fun mp var -> MAP.add var (a_elem (gen())) mp) MAP.empty fv;;
					
				
let infer_simp_type lmb = let system, tp = infer_simp_type_helper lmb (init_free_vars_types lmb) in 
	print_string ("type_t="^(st_to_string (alg_to_simp tp))^"\n");
	print_string "system\n";
	List.iter (fun (a, b) -> print_string ((alg_to_str a)^"="^(alg_to_str b)^"\n")) system;
	print_string "end\n";
							match Hw2_unify.solve_system system with 
							None -> None
							| Some ls -> Some (List.map (fun (a, b) -> (a, alg_to_simp b)) ls, 
							alg_to_simp (Hw2_unify.apply_substitution ls tp));;

let l1 = Hw1.lambda_of_string("\\x. x \\x. x");;

let func x = 
			
			let ans = infer_simp_type x in
			match ans with 
				None -> print_string "No type\n"
				| Some (ls, tp) -> print_string ((st_to_string tp)^"\n");;

List.iter func [l1];;

			
			
exception NoTypeExists;;

(* Apply substitutions to type tp except variables listed in blocked *)
(* HM_type -> Map -> Set -> HM_type *)
let rec rename tp substitutions blocked = match tp with
	HM_Elem v -> if (MAP.mem v substitutions) = true && (SET.mem v blocked) = false then 
							MAP.find v substitutions
							else tp
	| HM_Arrow (lhs, rhs) -> HM_Arrow(rename lhs substitutions blocked, 
										rename rhs substitutions blocked)
	| HM_ForAll (name, er) -> HM_ForAll(name, rename er substitutions (SET.add name blocked));;

	
(* Generate new names for inner HM_ForAll variables and rename them *)
let rec crt_and_rename_vars tp map = match tp with 
	HM_ForAll (name, inner) -> crt_and_rename_vars inner (MAP.add name (HM_Elem (gen())) map)
	| _ -> rename tp map SET.empty;;
	
(* Apply substitution to type *)
let apply_subst_to_type tp subst = rename tp subst SET.empty;;
	
(* Apply substitution to another context *)
(* map -> map -> map *)
let apply_subst_to_context s1 context = 
	MAP.map (fun tp -> apply_subst_to_type tp s1) context;;

(* Substitutions composition *)
let subst_comp s1 s2 = 
	let temp = MAP.map (fun tp -> apply_subst_to_type tp s1) s2 in 
	MAP.fold (fun k v mp -> if MAP.mem k mp then mp else MAP.add k v mp) s1 temp;;
	
let rec free_vars_lmb_helper l blocked = match l with
	HM_Var var -> if (SET.mem var blocked) = true then SET.empty else SET.singleton var
	| HM_Abs (var, lmb) -> free_vars_lmb_helper lmb (SET.add var blocked)
	| HM_App (lhs, rhs) -> SET.union (free_vars_lmb_helper lhs blocked) (free_vars_lmb_helper rhs blocked)
	| HM_Let (var, e1, e2) -> SET.union (free_vars_lmb_helper e1 blocked) (free_vars_lmb_helper e2 (SET.add var blocked));;
(* Get free vars of hm_lambda *)
let rec free_vars_lmb lmb = free_vars_lmb_helper lmb SET.empty;;


let rec free_vars_tp_helper tp blocked = match tp with 
	HM_Elem var -> if SET.mem var blocked then SET.empty else SET.singleton var 
	| HM_Arrow (lhs, rhs) -> SET.union (free_vars_tp_helper lhs blocked) (free_vars_tp_helper rhs blocked)
	| HM_ForAll (var, t) -> free_vars_tp_helper t (SET.add var blocked);;
(* Get free vars of hm_type *)
let rec free_vars_tp tp = free_vars_tp_helper tp SET.empty;;

(* Get free vars of context *)
let rec free_vars_context context = 
		MAP.fold (fun var tp st -> SET.union st (free_vars_tp tp)) context SET.empty;;

(* Zamykanie contexta *)		
let rec zamyk context tp = let fvtp = free_vars_tp tp in		
							let fv_cont = free_vars_context context in	
							SET.fold (fun tp res -> if SET.mem tp fv_cont then res else HM_ForAll (tp, res)) fvtp tp;;

(* Converts hm_type to algebraic_term *)
let rec hm_to_alg tp = match tp with
	HM_Elem var -> Hw2_unify.Var var 
	| HM_Arrow (lhs, rhs) -> Hw2_unify.Fun ("arrow", [hm_to_alg lhs; hm_to_alg rhs])
	| HM_ForAll (var, t) -> Hw2_unify.Fun ("forall", [Hw2_unify.Var var; hm_to_alg t]);;

(* Converts algebraic_term to hm_type *)
let rec alg_to_hm alg = match alg with 
	Hw2_unify.Var var -> HM_Elem var 
	| Hw2_unify.Fun ("arrow", f::s::[]) -> HM_Arrow (alg_to_hm f, alg_to_hm s)
	| Hw2_unify.Fun ("forall", (Hw2_unify.Var var)::s::[]) -> HM_ForAll (var, alg_to_hm s)
	| _ -> failwith "shouldn't be such algebraic term";;

	
let rec algorithm_w_impl lmb context = match lmb with 
	HM_Var a -> let tp = MAP.find a context in 
						(MAP.empty, crt_and_rename_vars tp MAP.empty)
	| HM_Abs (var, er) -> let e = HM_Elem (gen()) in
							let t = MAP.add var e context in
							let (s, tp) = algorithm_w_impl er t in
							(s, HM_Arrow (MAP.find var context, tp))
	| HM_App (lhs, rhs) -> let (s1, t1) = algorithm_w_impl lhs context in		
							let (s2, t2) = algorithm_w_impl rhs (apply_subst_to_context s1 context) in 
							let nw = HM_Elem (gen()) in 
							(match (Hw2_unify.solve_system 
									[(hm_to_alg (apply_subst_to_type t1 s2), 
									hm_to_alg (HM_Arrow (t2, nw)))]) with 
								None -> raise NoTypeExists
								| Some x -> let xmap = List.fold_left 
									(fun mp q -> mp) MAP.empty x in
									let s = subst_comp xmap (subst_comp s1 s2) in 
									(s, apply_subst_to_type nw s)
									)
									
	| HM_Let (var, e1, e2) -> 
							let (s1, t1) = algorithm_w_impl e1 context in							
							let nw_cont = apply_subst_to_context s1 context in 
							let nw_cont_fin = (MAP.add var (zamyk nw_cont t1) nw_cont) in 
							let (s2, t2) = algorithm_w_impl e2 nw_cont_fin in
							(subst_comp s2 s1, t2);;

let algorithm_w lmb = let fv_lm = free_vars_lmb lmb in
					  let context = SET.fold (fun var mp -> MAP.add var (HM_Elem (gen())) mp) fv_lm MAP.empty in
						try let (s, tp) = algorithm_w_impl lmb context in 
							Some (MAP.bindings s, tp)
						with _ -> None;;

