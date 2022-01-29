
(*p

\usepackage{a4wide}
\usepackage{alltt}
\usepackage{url}

\title{Lambda Calculus Evaluator in Ocaml}
\author{Christophe Deleuze}
\date{11 April, 2008}
\AtBeginDocument{\maketitle}

*)

(*s Introduction *)

(*
This document is a lambda calculus evaluator with tracing
facilities, coded in Objective Caml \cite{ocaml}.  It is written as a
litterate program, using the ocamlweb \cite{ocamlweb} tool.
*)

(*s Lambda terms *)

(* Here is the type of lambda terms.  We use the ``classical'' form
  with variable names, so we will have to perform alpha conversion
  sometimes.  An alternative would be to use De Bruijn's nameless
  dummies \cite{bruijn72lambda}.  [Hole] and [Here] are not part of
  lambda terms proper but will be useful in contexts for tracing
  reductions. *)

type term =
    Var of string | Abs of string * term | App of term * term
  | Hole | Here of term


(*s Alpha-conversion *)

(* To perform alpha conversion, we first have to find what are the
  free variables in a term [t].  These are all variables appearing in
  [t] except for occurences appearing under a lambda binding them.  We
  simply concat lists of variables appearing in subterms, filtering
  out the bound variable at each [Abs] node.  We don't mind that
  variables appear multiple times in our list.  *)

let rec fv t =
  match t with
  | Var x -> [ x ]
  | Abs(x,l) -> List.filter (fun e -> e<>x) (fv l)
  | App(t1,t2) -> fv t1 @ fv t2

(* So here is alpha conversion.  In term [t] this function renames all
   bound variables whose name is in [names].  Renaming is performed by
   suffixing [nb] to the variable name.  A fresh suffix will have to
   be provided at each call.  *)

let alpha names nb t =
  let rec alpha bound t =
    match t with
      | Var s -> if List.mem s bound then Var (s^nb) else t
      | App(l1,l2) -> App(alpha bound l1, alpha bound l2)
      | Abs(s,l)   -> 
	if List.mem s names then
	  Abs(s^nb, alpha (s::bound) l) 
	else 
	  Abs(s,alpha bound l)
  in
  alpha [] t

(*s Beta-reduction *)

(* Here is substitution, performing body$[$s/arg$]$ but assuming no
   variable captures can occur, i.e.  alpha conversion has already
   been performed if necessary. *)

let rec ssubst body s arg =
  match body with
  | Var s'     -> if s=s' then arg else Var s'
  | App(l1,l2) -> App(ssubst l1 s arg, ssubst l2 s arg)
  | Abs(o,l)   -> if o=s then body else Abs(o, ssubst l s arg)


(* Now, the real beta reduction, first performing alpha conversion to
   avoid variable captures.  [gen_nb] provides the unique number for
   the suffix we mentionned above ; [init_nb] resets the generator.
   What kind of variables can be captured?  These are free variables
   in [arg] that are bound in [body].  So we rename in [body] bound
   variables that appear free in [arg]. %ZZZ autre ? *)

let gen_nb, init_nb = 
  let nb = ref 0 in (fun () -> incr nb; !nb), (fun () -> nb := 0)
;;

let beta (App(Abs(s,body), arg)) =
  let nb = "-" ^ string_of_int (gen_nb()) in
  ssubst (alpha (fv arg) nb body) s arg


(*s Evaluation*)

(* We now have what we need to build evaluation functions.  Here's
call by name. *)

let rec cbn t =
  match t with
  | Var _ -> t
  | Abs _ -> t
  | App(e1,e2) -> let e1' = cbn e1 in
    match e1' with
    | Abs _ -> cbn (beta (App(e1', e2)))
    | _      -> App(e1', e2)
;;

(* Normal order evaluation can be built on top of call by name, as is
shown in \cite{sestoft02demonstrating}.  %ZZZ explications ? *)

let rec nor t =
  match t with
  | Var _ -> t
  | Abs(x,e) -> Abs(x,nor e)
  | App(e1,e2) -> let e1' = cbn e1 in
    match e1' with
    | Abs _ -> nor (beta (App(e1', e2)))
    | _ -> let e1'' = nor e1' in
      App(e1'',nor e2)


(*s Printing lambda terms *)

(* Lambda symbols will be printed as slashes `\texttt{/}'.  Printing
of terms can be performed by a simple recursive traversal.  However, since
such printing is intended for humans to read, we want to print them
somehow nicely, taking into account the following two rules:

   \begin{itemize}
   \item do not print parentheses when not necessary: application is
      left-associative,
   \item successive abstractions are grouped:
      print \texttt{/fx.fx} instead of \texttt{/f./x.fx}
   \end{itemize}

   For this we need a little bit of context information to decide how
   to precisely print a subterm, here it is:

   \begin{itemize}
   \item [Root]: current term has no father,
   \item [Lambda]: current term is just under a lambda,
   \item [LApp]: current term is the left son of an [App] node,
   \item [RApp]: current term is the right son of an [App] node.
   \end{itemize}

   As we previously said [Hole] and [Here] are for contexts, we will
   come back to this later.
 *)

type upnode = Root | Lambda | LApp | RApp

let rec string_of_term t =
  let rec sot up = function
    | Var s -> s
    | Abs(v,body) -> begin
	let p,s = match up with
	| Lambda -> "", ""
	| Root   -> "/",""
	| LApp
	| RApp   -> "(/",")"
	in
	p ^ v ^ (match body with Abs _ -> "" | _ -> ".") ^ sot Lambda body ^ s
    end
    | App(f,arg) ->
	let p,s = if up=RApp then "(",")" else "","" in
	p ^ (sot LApp f) ^ (sot RApp arg) ^ s

    | Hole -> " <> "
    | Here l -> " < " ^ string_of_term l ^ " > "
  in
  sot Root t
;;

(*s Managing the environment *)

(*

  The environment is a set of named terms.  We implement the
  environment as a global hash table binding strings to [term]s.  *)

let env = Hashtbl.create 30;;

let get_env n =
  try
    Hashtbl.find env n
  with _ -> failwith ("not in env: " ^ n)
;;

let set_env n t =
  Hashtbl.add env n t
;;

(*s Parsing lambda terms: lexical *)

(* For parsing, printing, and user convenience, names refering to the
  environment are introduced by the underscore character like in
  \verb+/x._fact x+.  Such a name is ended by any non letter
  character.  An alternative would be to force separation of single
  character variable names, as in \verb+/f x.f x+ but this would make
  terms much longer so we prefer the underscore trick.  All letters
  non following an underscore each stand for a variable name.  *)


(* We start with the lexical analyzer.  It'll get a string, turn this
into a character stream and build a token stream out of it.  Here's
the set of lexical tokens. *)

type token =  CHAR of char | LPAR | RPAR | DOT | LAMBDA | STRING of string

(* [soc] is short for [string_of_char].  [implode] turns a list of
characters into a string made of these characters in the reverse
order.  This will be used to build [STRING] tokens. *)

let soc = Printf.sprintf "%c"

let implode l =
  let rec imp l acc =
    match l with 
    | [] -> acc
    | h::t -> imp t ((soc h)^acc)
  in
  imp l ""
;;

(* [get_name] reads characters from the character stream and
cons-accumulates them until a non letter character is found.  It
returns the string of the accumulated characters in the initial order
by calling [implode].  *)

let get_name s =
  let rec loop acc =
    let n = Stream.peek s in
    if n = None then acc
    else
      let c = match n with Some c -> c in
      match c with
      | '_' | '/' | '(' | ')' | '.' | ' ' -> acc
      | _ -> Stream.next s; loop (c::acc)
  in
  implode (loop [])
;;

(* The lexer function takes a string and returns a token stream.  It
first turns the string into a character stream, then consumes them
producing tokens.  When an underscore character is found, all
following letters are accumulated by [get_name] to form a [STRING]
token.  Blanks are simply skipped.  All other characters directly map
to a token. *)

let lexer s =
  let s = Stream.of_string s
  in
  let rec next _ =
    let n = Stream.peek s in
    if n = None then None else
    match Stream.next s with
    | '_' -> Some(STRING (get_name s))
    | '/' -> Some LAMBDA
    | '(' -> Some LPAR
    | ')' -> Some RPAR
    | '.' -> Some DOT
    | ' ' -> next 0
    | c   -> Some (CHAR c)
  in
  Stream.from next
;;

(*s Parsing lambda terms: syntax *)

(* We now turn to the parsing proper.  Our LL(1) grammar for lambda
terms is (term being the axiom):

\newcommand{\fl}{\ensuremath{\rightarrow}}

\bigskip
\begin{tabular}{lll}
term & \fl &elt rest $\vert$ lamb \\
rest & \fl &elt rest $\vert$ $\varepsilon$ \\
elt &  \fl & [(CHAR c)] $\vert$ [LPAR] term [RPAR] \\
lamb & \fl & [LAMBDA] [(CHAR c)] lamb2 \\
lamb2 & \fl & [DOT] term $\vert$ [(CHAR c)] lamb2
\end{tabular}
\bigskip

The lamb2 rule allows compact notation for succession of lambdas:
   
   \texttt{/fnx.x} would be parsed this way

\begin{alltt}
   term -> lamb -> / f lamb2 -> / f n lamb2 -> / f n x lamb2
   -> / f n x . term -> / f n x . elt rest -> / f n x . x \(\varepsilon\)
\end{alltt}

*)


(* We will build our top-down parser using Caml streams, so we first
need to load in stream syntax.  *)

#use "topfind";;
#camlp4o;;

(* Caml built-in parsers exactly mimic the grammar.  Top-down parsers
``naturally'' making operators right-associative, note how [App] is
parsed as left-associative by using an accumulator in [rest] (tree for
successive applications is built left-to-right, bottom-up)\footnote{Of
course this is only possible because it's a degenerated tree.} *)

let rec term = parser
  | [< e=elt; t=rest e >] -> t
  | [< l=lamb >] -> l
and rest e1 = parser
  | [< e2=elt; e=rest(App(e1,e2)) >] -> e
  | [< >] -> e1
and elt = parser
  | [< 'CHAR c >] -> Var (soc c)
  | [< 'LPAR; t=term; 'RPAR >]  -> t
  | [< 'STRING s >] -> get_env s
and lamb = parser
  | [< 'LAMBDA; 'CHAR c; s=lamb2 >] -> Abs(soc c,s)
and lamb2 = parser
  | [< 'DOT; t=term >] -> t
  | [< 'CHAR c; s=lamb2 >] -> Abs(soc c,s)

(* Here is the final function for turning a string into a term. *)

let term_of_string s = term (lexer s)




(*s Tracing reductions *)

(* In order to trace reductions, we will need the following:

\begin{itemize}

\item the beta reduction function will have to print the term before
and after reduction,

\item the printed term should show somehow the current redex,

\item the recursive functions [cbn] and [nor] will have to maintain
the context of the current term and pass it to the beta reduction
function for it to print the whole term.

\end{itemize}

A context is a lambda term with a single [Hole].  A subterm in context
is a term appearing under a [Here] node in its context term.  See
[string_of_term] above to see the string representation.

*)

(* [put_in_hole] puts expression [e] in hole of context [c].  This can
   be used to extend a context by setting [e] as a sub-context of [c]
*)

let put_in_hole c e =
  let rec pih c =
    match c with
    | Hole -> e
    | Abs(s, Hole) -> Abs(s,e)
    | App(e1,Hole) -> App(e1,e)
    | App(Hole,e2) -> App(e,e2)
    | Abs(s, o) -> Abs(s, pih o)
    | App(o1,o2) -> App(pih o1, pih o2)
    | Var _ -> c
  in
  pih c

(* We have to maintain the context during recursive evaluation, but
using [put_in_hole] at each step will be very costly.  Instead, we
will accumulate a list of context steps, and build the corresponding
context only when we need it. %ZZZ

[buildc] builds the context from a list of context steps.  This is
done by putting the last step in the hole of previous one, putting the
obtained term in hole of previous context step etc.  *)

let buildc c =
  let rec soc acc c =
    match c with
    | [] -> acc 
    | h::t -> soc (put_in_hole acc h) t
  in
  soc Hole (List.rev c)


(* Now, given a list of context steps [c] and an expression [e], we
   build the term showing [e] in its context.  That is, we insert [e]
   under a [Here] in the context built from the list of context
   steps. *)

let put_in_context c e =
  match c with
  | h::t -> buildc ((put_in_hole h (Here e))::t)
  | _ ->  Here e

(* This one just puts [e] at its place in [c], without adding a [Here]
node. %ZZZ peut être traité à l'impression *)

let put_in_context2 c e =
  match c with
  | h::t -> buildc ((put_in_hole h e)::t)
  | _ ->  e


(* Evaluation functions will take as argument a function [beta] that will
   perform the beta reduction on the given sub-term.  It will receive
   as first argument a list of context steps for a possible
   side-effect. *)

(* Here, [tsub] prints the term in context before reduction, performs
   reduction, prints the reduced term in context, prints the whole
   reduced term with context marks and returns the reduced term.
   [tsubf] prints only the resulting reduced term.  *)

let tsub ctxt t = 
  print_string (">   " ^ (string_of_term (put_in_context ctxt t)) ^ "\n");
  let t' = beta t
  in
  print_string ("<   " ^ (string_of_term (put_in_context ctxt t')) ^ "\n");
  print_string ("=   " ^ (string_of_term (put_in_context2 ctxt t')) ^ "\n");
  t'

let tsubf ctxt t = 
  let t' = beta t
  in
  print_string ("=   " ^ (string_of_term (put_in_context2 ctxt t')) ^ "\n");
  t'

(* [tsub2] does the same thing, waiting for the return key to be
   pressed between each step. *)

let key () = flush stdout; input_char stdin;;

let tsub2 ctxt t = 
  print_string (">   " ^ (string_of_term (put_in_context ctxt t)) ^ "\n"); 
  key();
  let t' = beta t
  in
  print_string ("<   " ^ (string_of_term (put_in_context ctxt t')) ^ "\n");
  key();
  print_string ("=   " ^ (string_of_term (put_in_context2 ctxt t')) ^ "\n");
  key();
  t'

(*s New evaluation functions *)

(* We rewrite our evaluation functions so that they maintain context
steps and take the beta reduction function as a parameter.  Here's
call by name (we need to pass a context steps arg because [cbn] can be
called from [nor] below): *)

let cbn beta ctxt t =
  let rec cbn ctxt t =
    match t with
    | Var _ -> t
    | Abs _ -> t
    | App(e1,e2) -> let e1' = cbn (App(Hole,e2)::ctxt) e1 in
      match e1' with
(*i ERR Abs _ -> cbn (App(e1',Hole)::ctxt) (beta ctxt (App(e1', e2))) i*)
	Abs _ -> cbn ctxt (beta ctxt (App(e1', e2)))
      | _ -> App(e1', e2)
  in
  cbn ctxt t
;;

(* And normal order evaluation: *)

let nor beta t =
  let rec nor ctxt t =
    match t with
    | Var _ -> t
    | Abs(x,e) -> Abs(x, nor (Abs(x,Hole)::ctxt) e)
    | App(e1,e2) -> let e1' = cbn beta (App(Hole,e2)::ctxt) e1 in
      match e1' with 
	Abs _ -> nor ctxt (beta ctxt (App(e1', e2)))
      | _ -> let e1'' = nor (App(Hole,e2)::ctxt) e1' in
	App(e1'', nor (App(e1'',Hole)::ctxt) e2)
  in
  nor [] t
;;

(* Traced and stepped normal order evaluation.  We reset the number
generator at each use: *)

let trace s = init_nb(); nor tsubf (term_of_string s)
;;

let step s = init_nb(); nor tsub2 (term_of_string s);;

(* Non traced normal order evaluation.  This one does not use the
context steps that are being accumulated. *)

let nnor s = init_nb(); nor (fun c t -> beta t) (term_of_string s)
;;


(*s Basic constructs *)

(* To be able to play with the system, we define some useful basic
constructs. *)

let add_env n s =
  let t = term_of_string s in
  set_env n t
;;

add_env "succ" "/nfx.f(nfx)";
add_env "pred" "/nfx.n(/gh.h(gf))(/u.x)(/u.u)";
add_env "mult" "/nm./fx.n(mf)x";
add_env "exp"  "/mn.nm";
add_env "zero" "/fx.x";
add_env "true" "/xy.x";
add_env "false" "/xy.y";
add_env "iszero" "/n.n(/x._false)(_true)";
add_env "Y" "/g.(/x.g(xx))(/x.g(xx))";

(* We have all we need to define the factorial function. *)

add_env "ofact" "/fn.(_iszero n)(_succ _zero)(_mult n(f(_pred n)))";
add_env "fact"  "_ofact(_Y _ofact)";;

(*i(* another fixpoint combinator *)

add_env "Z" "/f.(/x. f(/y.xxy)) (/x. f(/y.xxy))"
;;
i*)

(*s Trying it out *)

(* We're done.  Just call [trace] with a string encoding your term and
watch its evaluation proceed.  Here are a few examples:

\begin{alltt}
# trace "_succ (/fx.f(fx))";;
=   /fx.f((/fx.f(fx))fx)
=   /fx.f((/x.f(fx))x)
=   /fx.f(f(fx))
- : term =
Abs ("f", Abs ("x", App (Var "f", App (Var "f", App (Var "f", Var "x")))))
# trace "_pred (/fx.fx)";;
=   /fx.(/fx.fx)(/gh.h(gf))(/u.x)(/u.u)
=   /fx.(/x.(/gh.h(gf))x)(/u.x)(/u.u)
=   /fx.(/gh.h(gf))(/u.x)(/u.u)
=   /fx.(/h.h((/u.x)f))(/u.u)
=   /fx.(/u.u)((/u.x)f)
=   /fx.(/u.x)f
=   /fx.x
- : term = Abs ("f", Abs ("x", Var "x"))
# trace "_fact (/fx.fx)";;
=   (/n.(/n.n(/xxy.y)(/xy.x))n((/nfx.f(nfx))( ...
...
=   /fx.(/fx25.f((/fx25.x25)fx25))fx
=   /fx.(/x25.f((/f43x25.x25)fx25))x
=   /fx.f((/f43x25.x25)fx)
=   /fx.f((/x25.x25)x)
=   /fx.fx
- : term = Abs ("f", Abs ("x", App (Var "f", Var "x")))
# trace "_fact (/fx.f(f(fx)))";;
=   (/n.(/n.n(/xxy.y)(/xy.x))n((/nfx.f(nfx))(/fx.x))...
... about 675 steps skipped
=   /fx.f(f(f(f(f(fx)))))
- : term =
Abs ("f",
 Abs ("x",
  App (Var "f",
   App (Var "f",
    App (Var "f", App (Var "f", App (Var "f", App (Var "f", Var "x"))))))))
\end{alltt}

Good, fact 3 is indeed 6!
*)

(*
\bibliography{biblio2}
\bibliographystyle{plain}

\end{document}
*)

(*s CPS *)

let new_var =
  let nb = ref 0 in
  fun () -> incr nb; "z~" ^ (string_of_int !nb)

let rec cps t =
  match t with
  | Var x -> Abs("k", App(Var "k", Var x))
  | Abs(x,t) -> Abs("k", App(Var "k",(Abs(x, cps t))))
  | App(a,b) -> 
      Abs("k", App(cps a,
		   Abs("a", (App(cps b,
				  Abs("b", App(App(Var "a", Var "b"),
						Var "k")))))))
let rec rcps t =
  match t with
  | Abs(k,App(Var k1, Var x)) when k=k1 -> Var x
  | Abs(k,App(Var k1, Abs(k',App(Var k1', (Abs(x,ca))))))
    when k=k1 && k'=k1' -> Abs(x,rcps ca)
  | Abs(k,App(ca, Abs(va,App(cb,
			     Abs(vb,App(App(Var va1, Var vb1), Var k1)))))) 
    when k=k1 && va=va1 && vb=vb1 ->
      App(rcps ca, rcps cb)
  | any -> any

(*s Drawing terms as trees *)

(* It would also be nice to draw lambda terms as trees.  For this, we
will use the tree module \cite{tree}. *)

open Tree;;

(*  Here's a function to turn a
lambda term into a tree as defined in the tree module.  *)

let rec tree_of_term l = 
  match l with
    Var s      -> Leaf s
  | Abs(s,l1)  -> Node("/" ^ s, [tree_of_term l1])
  | App(l1,l2) -> Node("·", [tree_of_term l1] @ [tree_of_term l2])
  | Hole       -> Leaf "<>"
  | Here(l1)   -> Node("< >", [tree_of_term l1])


(* The reduction function with graphic tracing.  Show current redex in
context before and after reduction, then the whole reduced term.
[gstep] is the evaluation fonction with graphic stepping.  *)

let gsub ctxt t = 
  clear_graph();
  to_sc (pict_of_tree (tree_of_term (put_in_context ctxt t)) A2local 0.) 10 50;
  read_key();
  let t' = beta t
  in
  clear_graph();
  to_sc (pict_of_tree (tree_of_term (put_in_context ctxt t')) A2local 0.) 10 50; 
  read_key();
  clear_graph();
  to_sc (pict_of_tree (tree_of_term (put_in_context2 ctxt t')) A2local 0.) 10 50;
  read_key();
  t'

let gstep s = init_nb(); open_graph ""; nor gsub (term_of_string s);;



(*s TODO

autre présentation :

context du ss-terme à réduire, ss-terme réduit, nouveau terme.

expliquer les context steps

représentation graphique : encadrer le redex, ou utiliser couleur, ne pas déplacer l'arbre (délicat ?)

possibilité de revenir en arrière

+ macros à l'évaluation

parsing des termes affichés xx19 -> App(Var"x", Var"x19")

possibilité réécriture en forme normale ?  /xx19.xx19 -> /fx.fx

evaluation / reduction ?

expliquer qu'une réalisation à la De Bruijn serait plus efficace mais
pas adpatée à un outil de démo/trace ?

*)



(*i
(* The set of lexical tokens. ZZZ Not really... SPACE...*)

type token =  CHAR of char | LPAR | RPAR | DOT | LAMBDA | STRING of string
            | SPACE | END

(* The lexer *)

let token_of_char = function
  | '/' -> LAMBDA
  | '(' -> LPAR
  | ')' -> RPAR
  | '.' -> DOT
  | ' ' -> SPACE
  | c   -> CHAR c

let soc = Printf.sprintf "%c"


let implode l =
  let rec imp l acc =
    match l with 
    | [] -> acc
    | h::t -> imp t ((soc h)^acc)
  in
  imp l ""
;;

let get_name s =
  let rec loop acc =
    let n = Stream.peek s in
    if n = None then acc
    else
      let c = match n with Some c -> c in
      match c with
      | '_' | '/' | '(' | ')' | '.' | ' ' -> acc
      | _ -> Stream.next s; loop (c::acc)
  in
  implode (loop [])

;;
let lexer s =
  let s = Stream.of_string s
  in
  let next _ =
    let n = Stream.peek s in
    if n = None then None else
    Some (match Stream.next s with
    | '_' -> STRING (get_name s)
    | '/' -> LAMBDA
    | '(' -> LPAR
    | ')' -> RPAR
    | '.' -> DOT
    | ' ' -> SPACE
    | c   -> CHAR c)
  in Stream.from next
;;


(* turn string into list of characters *)

let explode s =
  let rec exh acc = function
    | -1 -> acc
    | i  -> exh (s.[i]::acc) (pred i)
  in exh [ ] (pred (String.length s))

(* ZZZ ? *)

let implode l =
  let rec imp (h::t) acc =
    if h = '_' then acc
    else imp t ((soc h)^acc)
  in
  imp l ""
;;

(* Input string if first exploded into a list of characters, mapped to
a list of pseudo-tokens with a terminating END token.  

The only subtle point is the need to implode sets of CHARs whose first
is an underscore into a single STRING token.  This is what the fold is
doing, returning the true list of tokens, which is then turned into a
stream to be eaten by the parser.

  *)

let lexer s =
  let tl,_ =
    List.fold_left 
      (fun (toks,string) tok -> 
	match string,tok with
	  [], CHAR '_' -> toks,      ['_']
	| [], SPACE    -> toks,      []
	| [], END      -> toks,      []
	| [], tok      -> tok::toks, []
	| _,  CHAR c   -> toks,      c::string
	| _,  END      -> (STRING (implode string))::toks, []
	| _,  SPACE    -> (STRING (implode string))::toks, []
	| _,  tok      -> tok::(STRING (implode string))::toks, []
      )
      ([],[ ])
      ((List.map token_of_char (explode s)) @ [ END ])
  in Stream.of_list (List.rev tl)
;;
i*)
