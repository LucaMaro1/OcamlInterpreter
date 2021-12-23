type ide = string;;

type exp =
  | Eint of int
  | Ebool of bool
  | Den of ide
  | Prod of exp * exp
  | Sum of exp * exp
  | Diff of exp * exp
  |	Eq of exp * exp
  | Minus of exp
  | IsZero of exp
  | Or of exp * exp
  | And of exp * exp
  | Not of exp
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | FunCall of exp * exp
  | Letrec of ide * exp * exp
  | Dizionario of ide list * exp list
  | Insert of exp * ide * exp
  | Delete of exp * ide
  | HasKey of exp * ide
  | Filter of ide list * exp
  | Iterate of exp * exp
  | RecFun of ide * ide * exp  (* Funzione ricorsiva: nome, parametri, corpo della funzione *)
  | Fold of exp * exp;;

(* ambiente polimorfo *)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;; (* valuto una variabile sull'ambiente *)
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(* tipi esprimibili *)
type evT =
  Int of int
  | Bool of bool
  | Unbound
  | DizVal of ide list * exp list
  | FunVal of evFun
  | RecFunVal of ide * evFun
    and evFun = ide * exp * evT env;;

(* rts *)
(* type checking *)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
    Int(_) -> true
    |	_ -> false)
  | "bool" -> (match v with
    Bool(_) -> true
    | _ -> false) |
	_ -> failwith("not a valid type");;

(* funzioni primitive *)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u)
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		    (Int(n),Int(u)) -> Int(n+u)
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		    (Int(n),Int(u)) -> Int(n-u)
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u)
        | _ -> failwith("Typecheck error"))        
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	  Int(n) -> Int(-n)
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		    Int(n) -> Bool(n=0)
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		    (Bool(b),Bool(e)) -> (Bool(b||e))
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		    (Bool(b),Bool(e)) -> Bool(b && e)
        | _ -> failwith("Typecheck error"))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
        Bool(true) -> Bool(false)
        | Bool(false) -> Bool(true)
        | _ -> failwith("Typecheck error"))
  else failwith("Type error");;

let rec checkIntList expL = match expL with
  (* controlla che tutti gli elementi appartenenti alla lista siano interi *)
  [] -> true
  | h::t -> match h with
            | Eint(n) -> checkIntList t
            | _ -> false;;

let rec contains v lst = match lst with
  [] -> false
  | h::t -> if v = h then true
                     else contains v t;;

let rec search (lst: string list) (s: string) (acc: int) : int =
  (* conta dopo quanti passi trova l'elemento nella lista *)
  match lst with
  [] -> -1
  | h::t -> if h = s then acc
                     else search t s (acc + 1);;

let rec remove lst c =
  (* rimuove il c-esimo elemento *)
  match lst with
  [] -> failwith ("Input error")
  | h::t -> if c = 0 then t
                     else h::(remove t (c - 1));;

let rec selection il vl ilAcc lst cont = match il with
  (* aggiunge all'accumulatore le chiavi di lst e rimuove da vl i valori non corrispondenti alle chiavi che appartengono a lst *)
  (* infine ritorna un dizionario composto dall'accumulatore e da ciò che rimane della lista vl *)
  [] -> DizVal(ilAcc, vl)
  | h::t -> if (contains h lst) then selection t vl (ilAcc @ [h]) lst (cont + 1)
                                else selection t (remove vl cont) ilAcc lst cont;;

let filtr d lst = match d with
  (* restituisce un dizionario con le due liste filtrate *)
  | DizVal(il, vl) -> selection il vl [] lst 0
  | _ -> failwith("Type error");;

let rec duplicates_aux x lst = match lst with
  [] -> false
  | h::t -> if(x = h) then true
                      else duplicates_aux x t;;

let rec check_duplicates lst = match lst with
  [] -> false
  | h::t -> if (duplicates_aux h t) then true
                  else check_duplicates t;;

(* interprete *)
let rec eval (e : exp) (r : evT env) : evT = match e with
  | Eint n -> Int n
  | Ebool b -> Bool b
  | IsZero a -> iszero (eval a r)
  | Den i -> applyenv r i
  | Eq(a, b) -> eq (eval a r) (eval b r)
  | Prod(a, b) -> prod (eval a r) (eval b r)
  | Sum(a, b) -> sum (eval a r) (eval b r)
  | Diff(a, b) -> diff (eval a r) (eval b r)
  | Minus a -> minus (eval a r)
  | And(a, b) -> et (eval a r) (eval b r)
  | Or(a, b) -> vel (eval a r) (eval b r)
  | Not a -> non (eval a r)
  | Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
        else failwith ("nonboolean guard")
  | Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r))
  | Fun(i, a) -> FunVal(i, a, r)
  | FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				| FunVal(arg, fBody, fDecEnv) ->
            eval fBody (bind fDecEnv arg (eval eArg r))
        | RecFunVal(g, (arg, fBody, fDecEnv)) ->
					  let aVal = (eval eArg r) in
						  let rEnv = (bind fDecEnv g fClosure) in
							  let aEnv = (bind rEnv arg aVal) in
                  eval fBody aEnv
        | _ -> failwith("non functional value"))
  | Letrec(f, funDef, letBody) ->
    (match funDef with
        Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                                    eval letBody r1
        | _ -> failwith("non functional def"))
  | RecFun(nome, arg, body) -> RecFunVal(nome, (arg, body, r)) (* aggiungo l'ambiente alla funzione *)

  (* i dizionari sono composti da una lista di chiavi (stringhe) uniche e una lista della stessa lunghezza di interi *)
  | Dizionario(i, vl) -> if (check_duplicates i) then failwith("No key duplicates allowed")
                          else if (checkIntList vl) then
                                if (List.length i = List.length vl) then DizVal(i, vl)
                                                                    else failwith("Different number of values and keys")
                               else failwith("Only Integer values allowed")
  | Insert(d, i, v) -> (match (eval d r) with
                       | DizVal(il, vl) -> (match (eval (HasKey(d, i)) r) with
                                           | Bool(true) -> failwith("No key duplicates allowed")
                                           | Bool(false) -> if (typecheck "int" (eval v r)) then DizVal(il @ [i], vl @ [v])
                                                                                            else failwith("Only Integer values allowed")
                                           | _ -> failwith("HasKey error"))
                       | _ -> failwith("Type error, not a Dictionary"))
  | Delete(d, i) -> (match (eval d r) with
                     | DizVal(il, vl) -> let count = search il i 0 in
                                          if count = -1 then failwith("Key not found")
                                                        else DizVal((remove il count), (remove vl count))
                     | _ -> failwith("Type error, not a Dictionary"))
  | HasKey(d, i) -> (match (eval d r) with
                    | DizVal(il, vl) -> Bool(contains i il)
                    | _ -> failwith("Type error, not a Dictionary"))
  | Filter(idelist, d) -> let dizi = (eval d r) in
                          (match dizi with
                          | DizVal(il, vl) -> filtr dizi idelist
                          | _ -> failwith("Type error, not a Dictionary"))
  | Iterate(foo, d) -> (match (eval d r) with
                       | DizVal(il, vl) -> let rec iterate lst f amb = (match lst with (* iterate: funzione ausiliaria per eseguire foo su tutti gli elementi del dizionario *)
                                            [] -> []
                                            | h::t -> (match f with
                                                      | Fun(i , e) -> (match (eval f amb) with
                                                                      | FunVal(arg, fBody, fDecEnv) -> (match (eval fBody (bind fDecEnv arg (eval h amb))) with
                                                                                                       | Int(n) -> Eint(n)::(iterate t f amb) (* perché un dizionario contiene una lista di espressioni *)
                                                                                                       | _ -> failwith("Type error, function return a non Integer value"))
                                                                      | _ -> failwith("Eval error"))
                                                      | RecFun(nome, a, body) -> let fClosure = (eval f amb) in
                                                                                  (match fClosure with
                                                                                  | RecFunVal(g, (arg, fBody, fDecEnv)) -> 
                                                                                    let aVal = (eval h amb) in
                                                                                      let rEnv = (bind fDecEnv g fClosure) in
                                                                                        let aEnv = (bind rEnv arg aVal) in
                                                                                          (match (eval fBody aEnv) with
                                                                                          | Int(n) -> Eint(n)::(iterate t f amb) (* perché un dizionario contiene una lista di espressioni *)
                                                                                          | _ -> failwith("Type error, function return a non Integer value"))
                                                                                  | _ -> failwith("Eval error"))
                                                      | _ -> failwith("Non functional value"))) in
                                            DizVal(il, iterate vl foo r) (* chiamata funzione ausiliaria *)
                       | _ -> failwith("Type error, not a Dictionary"))
  | Fold(foo, d) -> (match (eval d r) with
                    | DizVal(il, vl) -> let rec fold lst f amb = match lst with (* fold: funzione ausiliaria per eseguire foo su tutti gli elementi del dizionario *)
                                        [] -> Eint 0
                                        | h::t -> (match f with
                                                  | Fun(i , e) -> (match (eval f amb) with
                                                                  | FunVal(arg, fBody, fDecEnv) -> (match (eval fBody (bind fDecEnv arg (eval h amb))) with
                                                                                                  | Int(n) ->  Sum(Eint(n), (fold t f amb))
                                                                                                  | _ -> failwith("Type error, function return a non Integer value"))
                                                                  | _ -> failwith("Eval error"))
                                                  | RecFun(nome, a, body) -> let fClosure = (eval f amb) in
                                                    (match fClosure with
                                                      | RecFunVal(g, (arg, fBody, fDecEnv)) -> 
                                                        let aVal = (eval h amb) in
                                                          let rEnv = (bind fDecEnv g fClosure) in
                                                            let aEnv = (bind rEnv arg aVal) in
                                                              (match (eval fBody aEnv) with
                                                              | Int(n) -> Sum(Eint(n), (fold t f amb))
                                                              | _ -> failwith("Type error, function return a non Integer value"))
                                                      | _ -> failwith("Eval error"))
                                                  | _ -> failwith("Non functional value")) in
                                        eval (fold vl foo r) r (* chiamata funzione ausiliaria *)
                      | _ -> failwith("Type error, not a Dictionary"));;



(* CASI DI TEST *)

(* variabili utili per i test e funzioni di supporto *)
let env0 = emptyenv Unbound;;
let factBody = RecFun("fact", "x", Ifthenelse(Eq(Den "x", Eint 0), Eint 1, Prod(Den "x", FunCall(Den "fact", Diff(Den "x", Eint 1) ))) );;

(* funzioni di supporto *)
let rec supportPrintD d r = (match (eval d r) with
  |DizVal(il, vl) -> (match il with
                     [] -> Printf.printf "";
                     | hs::ts -> match vl with
                                 [] -> failwith("Wrong dictionary structure")
                                 | hv::tv -> match hv with
                                             | Eint(n) -> Printf.printf " %s: %d " hs n;
                                                          supportPrintD (Dizionario(ts, tv)) r
                                             | _ -> failwith("Function error"))
  | _ -> failwith("Eval error"));;

let printDictionary d =
  Printf.printf "[";
  (supportPrintD d env0);
  Printf.printf "]\n";;

let printVal d = match(eval d env0) with
  | Int(n) -> Printf.printf "-> %d\n" n
  | _ -> failwith("Type error");;

(* variabili per dizionari *)
let d1 = Dizionario(["mele"; "banane"; "arance"; "pere"], [Eint(430); Eint(312); Eint(525); Eint(217)]);;
let d2 = Dizionario(["libri"; "dischi"; "quadri"], [Eint(12); Eint(45); Eint(3)]);;
let d3 = Dizionario(["uno"; "dieci"; "tre"], [Eint(1); Eint(10); Eint(3)]);;
let di1 = Insert(d1, "kiwi", Eint(85));;
let dr2 = Delete(d2, "quadri");;
let filteredDictionary = Filter(["mele"; "arance"; "pere"], di1);;
let funInc = Fun("x", (Sum(Den("x"), Eint(1))));;
let it1 = Iterate(funInc, d1);;
let it2 = Iterate(factBody, d3);;
let fold1 = Fold(funInc, d1);;
let fold2 = Fold(factBody, d3);;

(* valutazione dei dizionari creati in precedenza *)
Printf.printf "\nTEST PRINCIPALI:\n";;

Printf.printf "\n- Creo un dizionario:\n";;
printDictionary d1;;

Printf.printf "\n- Inserisco nel dizionario precedente un campo chiave-valore:\n";;
printDictionary di1;;

Printf.printf "\n- Creo un secondo dizionario:\n";;
printDictionary d2;;

Printf.printf "\n- Elimino un campo chiave-valore dal dizionario precedente:\n";;
printDictionary dr2;;

Printf.printf "\n- Eseguo la Filter su Insert(Dizionario([\"mele\"; \"banane\"; \"arance\"; \"pere\"], [Eint(430); Eint(312); Eint(525); Eint(217)]), \"kiwi\", Eint(85))\n";;
printDictionary filteredDictionary;;

Printf.printf "\n- Incremento di 1 tutti i valori del primo dizionario con la Iterate:\n";;
printDictionary it1;;

Printf.printf "\n- Sommo i valori del primo dizionario aumentati di 1 con la Fold:\n";;
printVal fold1;;

Printf.printf "\n- Creo un terzo dizionario:\n";;
printDictionary d3;;

Printf.printf "\n- Eseguo il fattoriale dei valori del terzo dizionario con la Iterate:\n";;
printDictionary it2;;

Printf.printf "\n- Eseguo il fattoriale dei valori del terzo dizionario e li sommo con la Fold:\n";;
printVal fold2;;

(* eccezioni *)
Printf.printf "\n\nTEST DELLE ECCEZIONI:\n";;

Printf.printf "\n- Provo a creare un dizionario con un valore booleano:\n";;
let fake_d1 = Dizionario(["mele"; "banane"; "arance"; "pere"], [Eint(430); Eint(312); Eint(525); Ebool(true)]);;
try printDictionary fake_d1
with _  as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo a creare un dizionario con chiavi che si ripetono:\n";;
let fake_d1 = Dizionario(["mele"; "banane"; "arance"; "mele"], [Eint(430); Eint(312); Eint(525); Eint(33)]);;
try printDictionary fake_d1
with _  as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo a creare un dizionario con un differente numero di chiavi e valori:\n";;
let not_a_d = Dizionario(["sballato"], [Eint(12); Eint(70)]);;
try printDictionary not_a_d
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad inserire una coppia chiave-valore nel primo dizionario, ma la chiave è già presente:\n";;
let dexeption = Insert(d1, "mele", Eint(90));;
try printDictionary dexeption
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad inserire una coppia chiave-valore nel primo dizionario, inserendo un valore booleano:\n";;
try printDictionary (Insert(d1, "pesche", Ebool(true)))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad inserire una coppia chiave-valore in un non dizionario:\n";;
try printDictionary (Insert(Eint(34), "pesche", Eint(2)))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo a cercare una chiave in un non dizionario:\n";;
try printDictionary (HasKey(Eint(34), "pesche"))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo a cancellare una coppia chiave-valore del primo dizionario, ma la chiave non è presente:\n";;
try printDictionary (Delete(d1, "kiwi"))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad eseguire la Iterate con una funzione che ritorna un valore booleano:\n";;
try printDictionary (Iterate(Fun("x", Ifthenelse(Eq(Den "x", Eint 1), Ebool(true), Ebool(false))), d1))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad eseguire la Iterate inserendo un Intero come funzione\n";;
try printDictionary (Iterate(Eint(7), d1))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad eseguire la Fold con una funzione ricorsiva che ritorna un valore booleano:\n";;
try printDictionary (Fold(RecFun("strange_fact", "x", Ifthenelse(Eq(Den "x", Eint 0), Ebool(true), FunCall(Den "strange_fact", Diff(Den "x", Eint 1)) ) ), d1))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad eseguire la Fold inserendo un Intero come funzione\n";;
try printDictionary (Fold(Eint(7), d1))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;

Printf.printf "\n- Provo ad eseguire la Fold su un non dizionario\n";;
try printDictionary (Fold(funInc, Eint(3)))
with _ as e -> Printf.printf "==> %s\n" (Printexc.to_string e);;