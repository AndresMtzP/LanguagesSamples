(*
* type: symbol definition (in HW1 / HW2))
*)
type ('nonterminal, 'terminal) symbol =
	| N of 'nonterminal
	| T of 'terminal;;

type ('nonterminal, 'terminal) parse_tree = 
	| Node of 'nonterminal * ('nonterminal, 'terminal) parse_tree list
	| Leaf of 'terminal

type 'terminal fragment = 'terminal list

type ('terminal, 'result) acceptor = 'terminal fragment -> 'result option

type ('terminal, 'result) matcher =
  ('terminal, 'result) acceptor -> 'terminal fragment -> 'result option

type ('nonterminal, 'terminal) parser = 
  'terminal fragment -> ('nonterminal, 'terminal) parse_tree


(*
	Problem 1. This warmup consists of converting a grammar from hw1 style, to hw 2 style. 
	To solve this problem, I utilize a helper function which takes any given rule 
	of the form (nonterminal, List of symbols) and simply outputs
	the list of symbols. The conversion is then done by utlizing Ocaml's list module to apply 
	the previous helper function to all nonterminals in a filtered grammar. 
*)
let convert_rule_to_prodfun rule = match rule with 
	| (nt, []) -> []
	| (nt, l) -> l

let convert_grammar gramml = match gramml with
	| (start, []) -> start, (fun nt -> [])
	| (start, rules) -> start, (fun nt -> 
				(List.map (fun rule -> convert_rule_to_prodfun rule) 
				(List.filter (fun (nont, _) -> nont = nt) rules)))


(*
	Problem 2. This simple problem recursively traverses a tree, returning lists of terminals as map function
	This list is then concatanated to generate the final parsing of the tree leaves 
	
*)
let rec parse_tree_leaves tree = match tree with
	| Node (_, treeList) -> List.concat (List.map parse_tree_leaves treeList)
	| Leaf l -> [l]   


(*
	Problem 3. This problem consists of building a matcher for a given grammar which returns a function which takes as input two arguments 
	acceptor and frag. The fragment is a given list of terminal symbols that we want to match. and the acceptor is a function which 
	takes as input a fragment and contains some logic as to whether a fragment is valid match.

	The approach used for this problem was that of mutual recursion. I use special matcher function for nonterminal symbols which calls   
	a rule matcher function to try to match the symbols inside the rule of the given nonterminal. Likewise, the rule_matcher function 
	iterates over the given list of symbols and for every nonterminal encountered, calls the previous nonterminal matcher, and when it 
	encounters a terminal, it simply tries to match to the next available symbol from the fragment.

	It is clear to see that a special approach is needed to prevent the algorithm from committing to a terminal match that will end up 
	not producing an acceptable overall match. To solve this, I make use of currying and partial functions. When the rule matcher encounters a 
	nonterminal I apply a partial function on the rest of the rule and feed this as an acceptor argument of the appropriate nonterminal matcher
	call. This way, when a terminal is encountered, the match will be done as a curried function, with right most symbol match cascading
	the result of the overall match.
*)

let accept_all : ('terminal, 'terminal fragment) acceptor = fun str -> Some str
let accept_empty_suffix : ('terminal, 'terminal fragment) acceptor =
  function
   | _::_ -> None
   | x -> Some x

(*
	Nont_matcher calls rule matcher to try to match a given rule in its entirety. If it fails, or the desired match was not found,
	call non_terminal matcher on the next rule, if there is one
*)
let rec nont_matcher (start, prodfun) nt rules = match rules with 
  | [] -> fun acceptor frag -> None
  | h::t -> fun acceptor frag ->
      let try_match_h = rule_matcher (start, prodfun) h acceptor frag in 
      (match try_match_h with
        | None -> nont_matcher (start, prodfun) nt t acceptor frag
        | _ -> try_match_h)

(*
	rule_matcher attempts to match a given rule in its entirety. In order to not commit to a possible failed traversal, we apply currying 
	via a partial evaluation of the remaining symbols after a nonterminal
*)
and rule_matcher (start, prodfun) rule = match rule with 
  | [] -> fun acceptor frag -> acceptor frag
  | (N h)::t -> fun acceptor frag -> let partial_acceptor = (rule_matcher (start, prodfun) t acceptor) in
  								nont_matcher (start, prodfun) h (prodfun h) partial_acceptor frag
  | (T h)::t -> fun acceptor frag -> (match frag with
  					| [] -> None
  					| ht::suf -> if not (ht = h) then None else rule_matcher (start, prodfun) t acceptor suf)

(*
	Make matcher simply calls nont_matcher on the start symbol. This function is partial, and results in a function acting
	on an acceptor and a fragment
*)
let make_matcher (start, prodfun) = 
  fun acceptor frag -> nont_matcher (start, prodfun) start (prodfun start) acceptor frag



(*
	Problem 4. Given that a parser has plenty of similarities with a matcher (e.g a parser is a matcher with 
	an empty_suffix acceptor) I decided to simply modify the algorithm used for the matcher and make it into a parser.
	The biggest problem with this approach was that of building the tree as the matching was taking place. Many failed 
	attempts resulted from trying to adapt an acceptor function to return tree nodes as it was being curryied through the function.

	After several failed attempts, the approach I decided to pursue was one in which minimal changes are done to the matcher to instead provide a 
	List of tuples (int, ParseTree), representing the path taken by the parser. To do this I modified an acceptor function 
	to take as input a tuple of fragment and list, and likewise give this as output to allow for currying the function throughout.

	As a second step with this approach, I built a function which recursively iterates over the reversed path found by the pathfinder,
	and attempts to insert each tree into the appropriate parent node

*)

(*
	Pathfinder acceptor is a modified version of the accept_empty_suffix acceptor. Given an empty fragment (wrapped in a tuple), return the 
	same tuple if the remaining suffix is empty. In other words, it only accpets a match if the fragment has been matched in its entirety
*)
let pathfinder_acceptor path = 
	match path with
    | (_::_), path -> None
    | x, path -> Some (x, path)


(*
	Same as nont_matcher above, except it also takes an argument level, which will tell us what level of the tree traversal the
	node was visited in. This will be used to build a path. 
*)
let rec nont_parser (start, prodfun) level nt rules = match rules with 
  | [] -> fun acceptor frag -> None
  | h::t -> fun acceptor frag ->
      let try_match_h = rule_parser (start, prodfun) level h acceptor frag in 
      (match try_match_h with
        | None -> nont_parser (start, prodfun) level nt t acceptor frag
        | _ -> try_match_h)

(*
	Same as rule matcher but also with a level argumetn addition. This function builds a path through currying. The resulting path, if any
	is found will be of the form [(1, Node(x []));(2, Leaf(y));(1 , Node(z, []))]. The root with value 0, is added to the path before
	transforming the path into a parsing tree
*)
and rule_parser (start, prodfun) level rule = match rule with 
  | [] -> fun acceptor frag -> acceptor frag
  | (N h)::t -> fun acceptor frag -> let partial_acceptor = (rule_parser (start, prodfun) level t acceptor) in
  								(match nont_parser (start, prodfun) (level + 1) h (prodfun h) partial_acceptor frag with
  								 | None -> None
  								 | Some (s, p) -> Some(s, (level, Node(h, []))::p)
  								)
  | (T h)::t -> fun acceptor frag -> (match frag with
  					| [], _ -> None
  					| (ht::suf), path -> if not (ht = h) then None 
  										else (match rule_parser (start, prodfun) level t acceptor (suf, path) with
  										| None -> None
  										| Some (s, p) -> Some(s, (level, Leaf(ht))::p)))

(*
	Insert into parent takes the first node of the reversed path (i.e the last node) and inserts it into the node of the first
	instance of a smaller level. In other words, the last node will be grouped into the first possible parent node. This function 
	is called for every element in the path, and could potentially have to traverse the entire list to find the parent node.
	 Not a promising complexity
*)
let rec insert_into_parent (level, pt) revpath =
	match revpath with
	| [] -> []
	| h::t -> (match h with
				| l, Node(nt, ptList) -> if level > l then (l, Node(nt, pt::ptList))::t else h::(insert_into_parent (level, pt) t)
				| _ -> h::(insert_into_parent (level, pt) t))

(*
	Helper function to transform path into parse tree
*)
let rec build_tree_helper revpath =
	match revpath with
	| [] -> None 
	| h::t -> let flattened_path = insert_into_parent h t in
			(match flattened_path with
			| (level, root)::[] -> Some root
			| [] -> None
			| _ -> build_tree_helper flattened_path )

(*
	Reverses function before calling the treehelper
*)
let rec build_parse_tree_from_path path =
	match path with
	| [] -> None
	| _ -> build_tree_helper (List.rev path)


(*
 The aptly-named pathfinder runs the nontparser function on the start symbol with a given fragment. Returns the grammar 
 traversal if a parsing was succesful
*)
let pathfinder (start, prodfun) = 
  fun frag -> 
  	match nont_parser (start, prodfun) (1) start (prodfun start) pathfinder_acceptor (frag, []) with
  	| None -> None
  	| Some (s, p) -> Some ((0, (Node(start, [])))::p)


(*
	Make_parse bundles all the previously mentioned functions and returns a function taking a fragment as an argument,
	returns the parsing tree of the fragment within a given grammar.
*)
let make_parser (start, prodfun) =
  fun frag -> let path = pathfinder (start, prodfun) frag in
  	match path with
  	  | None -> None
  	  | Some p -> build_parse_tree_from_path p 
