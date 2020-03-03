(*Define variant for filter_reachable function. 
To be used on grammar definitions*)
type ('a, 'b) symbol = N of 'a | T of 'b

(* 1. subset function: Check every item in a to see if it is included in b.
 All elements in a must be in b in order to be a subset*)
let subset a b = List.for_all (fun x -> List.exists (fun y -> y = x) b) a

(* 2. equal_sets function: Use subset function. 
a and b are the same set iff a is a subset of b, and viceversa*)
let equal_sets a b = (subset a b) && (subset b a)

(* 4. set_intersection function: Filter a to get a new list
 with only the items included also in b*)
let set_intersection a b = List.filter (fun x -> List.exists (fun y-> y = x) b) a

(* 5. set_diff function: Filter a to get a new list 
with only the items excluded from b *)
let set_diff a b = List.filter (fun x -> not (List.exists (fun y -> y = x) b)) a

(* 3. set_union function: Make use of previous functions. 
Concatanate difference of a and b, intersection of a and b, 
and difference of b and a*)
let set_union a b =
    (set_diff a b) @
    (set_intersection a b) @
    (set_diff b a)

(* 6. computed_fixed_point function: recursively evaluate the function 
from input argument, start with x input and evaluate until the result 
of f returns the same value as previous call*)
let rec computed_fixed_point eq f x = 
    let res = (f x) in	
    match x with 
    |	_ when eq x res -> x
    | 	_ -> computed_fixed_point eq f res


(*Helper function reachable: To be used in filter_reachable. 
Returns true if input tuple nt is reachable within input grammar g*)
let reachable nt g =
	match nt, g with
	|	_ , [] -> false 
	|	(nonterminal, rules), grammar ->
            List.exists 
			(fun (x1, x2) ->
				List.exists (fun y1 ->
					match y1 with 
						|	N nont when nont = nonterminal && nont != x1 -> true
						|	_ -> false) x2) grammar

(*Helper function filter_reachable_helper: To be used in filter_reachable.
This function filter input grammar g, with predicate being, a given rule 
not being reachable by using helper function reachable, it is needed
To evaluate this function several times to filter unreachable 
rules that might have survived first pass*)
let filter_reachable_helper g =
	match g with
	|	(start_sym, rules) when rules = [] -> g
	|	(start_sym, rules) -> (start_sym, List.filter 
				(fun rule -> 
					match rule with
					|	(nt, _) when nt != start_sym && not (reachable rule rules) -> false
					|	_, _ -> true) rules)

(* 7. filter_reachable function: Make use of computed_fixed_point 
function in order to call helper function several times, 
until we make sure no unreachable rule survives the filtering process*)
let filter_reachable g =
	computed_fixed_point (=) filter_reachable_helper g
