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
	Var v -> "(" ^ v ^ ")"
	| Abs (v, y) -> "(\\" ^ v ^ "." ^ (string_of_lambda y) ^ ")"
	| App (l, r) -> (string_of_lambda l) ^ " " ^ (string_of_lambda r);;

let beg_of_string x ind = String.trim (String.sub x 0 ind);;
let en x ind = String.trim (String.sub x ind ((String.length x) - ind));;
	
let rec lambda_of_string x = match (String.get x 0) with
	'\\' -> let ind = String.index x '.' in
			Abs (beg_of_string x ind, lambda_of_string (en x (ind + 1)))
	| '(' -> lambda_of_string (String.trim (String.sub x 1 ((String.length x) - 1)))
	| _ -> try let ind = String.index x ' ' in
				App (lambda_of_string (beg_of_string x ind), lambda_of_string (en x (ind + 1)))
									with 
			_ -> Var x;;
