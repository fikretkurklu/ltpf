(*KACHA Tom / MEIGNEN Hugo / KURKLU Fikret*)



(*1*)

(**1.1**)

(***1.1.1***)


(*type cons = U | Z
type var = A | B | C | D
type exp = Cons of cons | Var of var
type all = Prog of prog*b | Skip_a
and b = All of all | Skip_b
and prog =  Skip_p | Affect of var * exp | If of exp * all * all
             | While of exp * all*)

(***1.1.2***)

(*
    C ::= 0 | 1
    V ::= a | b | c | d
    E ::= V | C
    P ::= P;P | V:=E | i(E){P}{P} | w(E){P} | epsilon

    => recursive gauche
 *)

(***1.1.3***)

(*
    C ::= 0 | 1
    V ::= a | b | c | d
    E ::= V | C
    A ::= PB | epsilon
    B ::= ;A | epsilon
    P ::= V:=E | i(E){A}{A} | w(E){A} | epsilon
 *)

(**1.2**)

(***1.2.1***)

(* s,(P) -> c'        [| b |]s = true
   __________________________________   avec  c' =  (s',(P)) ou (s'!)
      s, (if b then P else Q) -> c'


 s,(P) -> c'        [| b |]s = false
   __________________________________   avec  c' =  (s',(Q)) ou (s'!)
      s, (if b then P else Q) -> c'
 *)


(***1.2.2***)

type cons = U | Z
type var = A | B | C | D
type exp = Cons of cons | Var of var | Hashtag
type all = Prog of prog*b | Skip_a
and b = All of all | Skip_b
and prog =  Skip_p | Affect of var * exp | If of exp * all * all
             | While of exp * all

(*
    C ::= 0 | 1
    V ::= a | b | c | d
    E ::= V | C | #
    A ::= PB | epsilon
    B ::= ;A | epsilon
    P ::= V:=E | i(E){A}{A} | w(E){A} | epsilon
 *)

(*2*)

(**2.1**)

(***2.1.1***)


type analist = char list -> char list
(* Le type des fonctions qui épluchent une liste et rendent un résultat *)
type ('r, 'term) ranalist = 'term list -> 'r * 'term list;;

exception Echec

let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

(* Non terminal vide *)
let epsilon : analist = fun l -> l

let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)

(* Choix entre a ou b informatifs *)
let (+|) (a : ('res, 'term) ranalist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> try a l with Echec -> b l

(* a sans résultat suivi de b sans résultat *)
let ( -->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : analist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b sans résultat *)
let (+->) (a : ('res, 'term) ranalist) (b : analist) : analist =
  fun l -> let (x, l) = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : ('resa, 'term) ranalist) (b : 'resa -> ('resb, 'term) ranalist) : ('resb, 'term) ranalist =
  fun l -> let (x, l) = a l in b x l


let p_C : (cons, char) ranalist = fun l -> l |>
  (terminal '0' -+> epsilon_res Z) +| (terminal '1' -+> epsilon_res U)

let p_V : (var, char) ranalist = fun l -> l |>
  (terminal 'a' -+> epsilon_res A) +| (terminal 'b' -+> epsilon_res B)
  +| (terminal 'c' -+> epsilon_res C) +| (terminal 'd' -+> epsilon_res D)

let p_E : (exp, char) ranalist = fun l -> l |>
  (p_C ++> fun c -> epsilon_res (Cons c))
  +| (p_V ++> fun v -> epsilon_res (Var v))
  +| (terminal '#' -+> epsilon_res Hashtag)

let rec p_A : (all, char) ranalist = fun l -> l |>
  (p_P ++> fun p -> p_B ++> fun b -> epsilon_res (Prog (p,b)))
  +| epsilon_res Skip_a
and p_B : (b, char) ranalist = fun l -> l |>
  (terminal ';' -+> p_A ++> fun a -> epsilon_res (All(a)))
  +| epsilon_res Skip_b
and p_P : (prog, char) ranalist = fun l -> l |>
  (p_V ++> fun v1 -> terminal ':' --> terminal '=' -+> p_E
      ++> fun e1 -> epsilon_res (Affect (v1, e1)))
  +| (terminal 'i' --> terminal '(' -+> p_E ++> fun e2 -> terminal ')' --> terminal '{'
      -+> p_A ++> fun p1 -> terminal '}' --> terminal '{' -+> p_A
      ++> fun p2 -> terminal '}' -+> epsilon_res (If(e2, p1, p2)))
  +| (terminal 'w' --> terminal '(' -+> p_E ++> fun e3 -> terminal ')' --> terminal '{'
      -+> p_A ++> fun p3 -> terminal '}' -+> epsilon_res (While (e3, p3)))
  +| epsilon_res Skip_p


(***2.1.2***)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

let test s = p_A (list_of_string s)


let p = test "a:=b;"
let p1 = test "a:=1;i(a){}{}"
let p1 = test "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}"
let p2 = test "a:=0;b:=1;c:=0;w(b){i(c){b:=0;a:=b}{c:=#}}"
let p3 = test "a:=1;b:=0;c:=1;w(a){i(b){w(c){c:=#;a:=0}}{b:=1;c:=a}}"

(**2.2**)
 
(***2.2.1***)
 
type state = cons list
 
let rec init0 (s : state) : state =
    match s with
    | [] -> []
    | a::s' -> U :: (init0 s')
 
let read (v : var)(s : state)(i : int) : cons =
    match v with
    | A -> List.nth s 0
    | B -> List.nth s 1
    | C -> List.nth s 2
    | D-> List.nth s 3
 
let value (e : exp)(s : state) : cons =
    match e with
    | Cons U -> U
    | Cons Z -> Z
    | Var A -> read A s
    | Var B -> read B s
    | Var C -> read C s
    | Var D -> read D s
    | _ -> raise Echec 
 
let rec int_update (s : state)(n : int)(c : cons) : state =
    match s with
    | [] -> []
    | a :: s' -> if n = 0 then c :: s' else a :: (int_update s' (n-1) c)
 
let var_update (s : state)(v : var)(e : exp) : state =
    match v with
    | A -> int_update s 0 (value e s)
    | B -> int_update s 1 (value e s)
    | C -> int_update s 2 (value e s)
    | D -> int_update s 3 (value e s)
 
let assign (l: char list) (s:state) =
  let l = p_A l in
  match l with
  | ((Prog (Affect (var, exp), Skip_b)), l)-> var_update s var exp
  | _ -> raise Echec
 
 
(***2.2.2***)
 
 
type config =
  | Inter of all*state
  | Final of state
 
let faire_un_pas prog s a = let s' = 
                              match prog with
                              | Skip_p -> Final(s)
                              | If(e, a1, a2) -> begin match e with
                                                 | Var(v) -> begin match read v s with
                                                             | U -> Inter(a1, s)
                                                             | Z -> Inter(a2, s) end
                                                 | Cons(U) -> Inter(a1, s)
                                                 | Cons(Z) -> Inter(a2, s)
                                                 | Hashtag -> raise Echec end
                              | While(e,a) ->  Inter(Prog(If(e, Prog(While(e,a), All(a)), Skip_a), Skip_b), s) 
                              | Affect (v, e) -> let s1 = var_update s v e in Final(s1) 
                            in (s', a + 1)
 
(***2.2.3***)
 
let executer prog =
  let rec aux p s nb = 
    match p with
    | Skip_a -> (s, nb)
    | Prog(a, All(e)) -> begin match a with
                        | While(_, _) -> let (res, nb) = aux e s nb in let next = faire_un_pas a res nb in
                                       begin match next with
                                       | (Inter(prg, et), nb) -> aux prg et nb
                                       | (Final(x), nb) -> (x, nb)
                                       end 
                        | _ -> let (res, nb) = faire_un_pas a s nb in
                               begin match res with
                               | Inter(prg, et) -> let (tmp, nb) = aux prg et nb in aux e tmp nb
                               | Final(x) -> aux e x nb
                               end
                        end
    | Prog(a, Skip_b) -> let (res, nb) = faire_un_pas a s nb in
                          begin match res with
                          | Inter(prg, et) -> aux prg et nb
                          | Final(x) -> (x, nb) end
  in aux prog [] 0



let (b, p) = (test  "a:=b;") in executer b;;


(**2.3**)
 
(*Voir partie Coq*)
 
(**2.4**)
 
(*Voir partie Coq*)
 
