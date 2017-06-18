type peano = Z | S of peano;; (* ???? ?????????? ?????????? ? ?????????? *)
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x = match x with 
	0 -> Z
	| n -> S(peano_of_int(n - 1));;

let rec int_of_peano p = match p with
    Z -> 0
  | S x -> 1 + int_of_peano x;;

let inc x = S x;;
let rec add x y = match x with
	Z -> y
	| S q -> S(add q y);;

let rec sub x y = match y with
	Z -> x
	| S yy -> match x with	
		Z -> Z
		| S xx -> sub xx yy;;
		
let rec mul x y = match y with 
	Z -> Z
	| S yy -> add (mul x yy) x;;
	
let rec power x y = match y with
	Z -> S Z
	| S yy -> mul (power x yy) x;;

let rec rev_append x y = match x with
	[] -> y
	| s::e -> rev_append e (s::y);;
	
	
let rec split_n l left right = match l with 
	[] -> (left, right)
	| h::t -> split_n t right (h::left);;			
let rec split x = split_n x [] [];;

let rec merge x y = match x with 
		[] -> y
		| xh::xt -> match y with 
			[] -> x
			| yh::yt -> if xh < yh then xh::(merge xt y)
						else yh::(merge x yt);;

let rec rev x = rev_append x [];;
	
let rec merge_sort x = match x with
	[] -> []
	| single::[] -> single::[]
	| head::tail -> let (left, right) = split x in
					merge (merge_sort left) (merge_sort right);;					
let rec string_of_lambda x = match x with
	Var v -> v 
	| Abs (v, y) -> "" ^ "\\" ^ v ^ "." ^ (string_of_lambda y) ^ ""
	| App (l, r) -> "(" ^ (string_of_lambda l) ^ ") (" ^ (string_of_lambda r) ^ ")";;

let beg_of_string x ind = String.trim (String.sub x 0 ind);;
let en x ind = String.trim (String.sub x ind ((String.length x) - ind));;

let rec find_pos x bal pos = match x.[pos] with 
	' ' -> if bal = 0 then pos else find_pos x bal (pos - 1)
	| ')' -> find_pos x (bal + 1) (pos - 1)
	| '(' -> if bal = 1 then pos else find_pos x (bal - 1) (pos - 1)
	| _ -> find_pos x bal (pos - 1);;

let rec get_lambda_pos x pos bal = match (bal, x.[pos]) with
	(0, '\\') -> pos - 1
	| (_, '(') -> get_lambda_pos x (pos + 1) (bal - 1)
	| (_, ')') -> get_lambda_pos x (pos + 1) (bal + 1)
	| (_, _) -> get_lambda_pos x (pos + 1) bal;;
	
let rec parse_application x = let pos = find_pos x 0 ((String.length x) - 1) in 
								if pos = 0 then lambda_of_string_helper (String.sub x 1 ((String.length x) - 2))
								else 
			try let lam_pos = get_lambda_pos x 0 0 in
				
				App (lambda_of_string_helper (beg_of_string x lam_pos), 
						lambda_of_string_helper (en x lam_pos))
			with _ -> 
								App (lambda_of_string_helper (beg_of_string x pos),
									lambda_of_string_helper (en x pos))

	
and lambda_of_string_helper x = match (String.get x 0) with
	'\\' -> let ind = String.index x '.' in		
			Abs (String.trim (String.sub x 1 (ind - 1)), lambda_of_string_helper (en x (ind + 1)))
	| _ -> if (String.contains x '(') || (String.contains x ' ') then	
				parse_application x
			else 
				Var x;;

let lambda_of_string x = lambda_of_string_helper (String.trim x);;
				
let print_lambda x = print_string ((string_of_lambda x)^"\n");;

let t2 = lambda_of_string "(\\a.a a)(\\a.a)";;
print_lambda t2;;
print_string(string_of_lambda(App(Var "x", App (Var "y", Var "z"))) ^ "\n");;
print_string(string_of_lambda(lambda_of_string("((\\x   .    \\y.(x (a b)) 	x y) z asd)")) ^ "\n");;
print_string(string_of_lambda(lambda_of_string("a \\x. y a")));;
print_string "\n\n\n\n";