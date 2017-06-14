type peano = Z | S of peano;; (* типы необходимо копировать в реализацию *)
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
	| Abs (v, y) -> "(" ^ "\\" ^ v ^ "." ^ (string_of_lambda y) ^ ")"
	| App (l, r) -> "(" ^ (string_of_lambda l) ^ ") (" ^ (string_of_lambda r) ^ ")";;

let beg_of_string x ind = String.trim (String.sub x 0 ind);;
let en x ind = String.trim (String.sub x ind ((String.length x) - ind));;


let rec clos x pos bal = match bal with
	0 -> pos
	| _ -> match (String.get x pos) with 
		'(' -> clos x (pos + 1) (bal + 1)
		| ')' -> clos x (pos + 1) (bal - 1)
		| _ -> clos x (pos + 1) bal;;
let rec back x pos bal = match bal with
	0 -> pos
	| _ -> match (String.get x pos) with 
		'(' -> back x (pos - 1) (bal - 1)
		| ')' -> back x (pos - 1) (bal + 1)
		| _ -> back x (pos - 1) bal;;

let rec get_lambda_pos x pos bal = match bal with
	0 -> match (String.get x pos) with
		"\\" -> pos - 1
		| _ -> get_lambda_pos x pos + 1 bal
	| _ -> match (String.get x pos) with 
		'(' -> get_lambda_pos x (pos - 1) (bal - 1)
		| ')' -> get_lambda_pos x (pos - 1) (bal + 1)
		| _ -> get_lambda_pos x (pos - 1) bal;;
		
let rec parse_application1 x = match (String.get x (String.length x - 1)) with
	')' -> 
	let last_space = back x (String.length x - 2) 1 in
		App (lambda_of_string (beg_of_string x last_space), lambda_of_string (en x last_space)) 
	| _ -> 
	try let pos = get_lambda_pos x in 
		App (lambda_of_string (beg_of_string x pos), lambda_of_string (en x pos))
		with 
	let last_space = String.rindex x ' ' in 	
		App (lambda_of_string (beg_of_string x last_space), lambda_of_string (en x last_space))
	
and lambda_of_string x = match (String.get x 0) with
	'\\' -> let ind = String.index x '.' in		
			Abs (beg_of_string x ind, lambda_of_string (en x (ind + 1)))
	| '(' -> 
			let pos = clos x 1 1 in
			if pos = (String.length x) then 
				lambda_of_string (String.trim (String.sub x 1 ((String.length x) - 2)))
			else 
				parse_application1(x)
	| _ -> try let ind = String.index x ' ' in
				parse_application1(x) with 
			_ -> Var x;;

print_string(string_of_lambda(App(Var "x", App (Var "y", Var "z"))) ^ "\n");
print_string(string_of_lambda(lambda_of_string("((\\x   .    \\y.(x (a b)) 	x y) z asd)")) ^ "\n");
print_string(string_of_lambda(lambda_of_string("a \\x. y")))