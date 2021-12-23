type ide = string;;

(* tipi esprimibili *)
type tval = 
  | Unbound
  | TInt
  | TBool
  | TFun of tval * tval
  | TDict;;

type texp =
  | EInt of int
  | EBool of bool
  | Den of ide
  | Add of texp * texp
  | Sub of texp * texp
  | Prod of texp * texp
  | Not of texp
  | And of texp * texp
  | Or of texp * texp
  | Ifthenelse of texp * texp * texp
  | Eq of texp * texp
  | Let of ide * texp * texp
  | Fun of ide * tval * tval * texp (* parametro, tipo del parametro, tipo di ritorno, definizione *)
  | LetRec of ide * texp * texp
  | FunCall of texp * texp
  | Dizionario of ide list * texp list
  | Insert of texp * ide * texp
  | Delete of texp * ide
  | HasKey of texp * ide
  | Filter of ide list * texp
  | Iterate of texp * texp
  | Fold of texp * texp;;


(* ambiente polimorfo *)
type tenv = ide -> tval;;
let emptyenv (v : tval) = function x -> v;;
let bind (r : tenv) (i : ide) (v : tval) = function x -> if x = i then v else r x;;

let rec checkIntList lst = match lst with
  [] -> true
  | h::t -> (match h with
            | EInt(n) -> checkIntList t
            | _ -> false);;
(* valutazione dei tipi *)
let rec teval e tenv = match e with
  | EInt i -> TInt
  | EBool b -> TBool
  | Den s -> tenv s
  | Let(i, e1, e2) -> let t = teval e1 tenv in
                        teval e2 (bind tenv i t)
  | Add (e1, e2) -> let t1 = teval e1 tenv in
                    let t2 = teval e2 tenv in
                      (match (t1, t2) with
                      | (TInt, TInt) -> TInt
                      | (_,_) -> failwith("WrongType"))
  | Sub(e1, e2) -> let t1 = teval e1 tenv in
                      let t2 = teval e2 tenv in
                        (match (t1, t2) with
                        | (TInt, TInt) -> TInt
                        | (_,_) -> failwith("WrongType"))
  | Prod(e1, e2) -> let t1 = teval e1 tenv in
                    let t2 = teval e2 tenv in
                      (match (t1, t2) with
                      | (TInt, TInt) -> TInt
                      | (_,_) -> failwith("WrongType"))
  | Not(e1) -> (match (teval e1 tenv) with
                | TBool -> TBool
                | _ -> failwith("WrongType"))
  | And(e1, e2) -> (match (teval e1 tenv) with
                    | TBool -> (match (teval e2 tenv) with
                                    | TBool -> TBool
                                    | _ -> failwith("WrongType"))
                    | _ -> failwith("WrongType"))
  | Or(e1, e2) -> (match (teval e1 tenv) with
                    | TBool -> (match (teval e2 tenv) with
                                    | TBool -> TBool
                                    | _ -> failwith("WrongType"))
                    | _ -> failwith("WrongType"))
  | Eq(e1, e2) -> if ((teval e1 tenv) = (teval e2 tenv)) then TBool
                                                         else failwith("WrongType")
  | Ifthenelse(e, e1, e2) -> let t = teval e tenv in
                            (match t with
                            | TBool -> let t1 = teval e1 tenv in
                                        let t2 = teval e2 tenv in
                                          (match (t1, t2) with
                                          | (TInt, TInt) -> TInt
                                          | (TBool, TBool) -> TBool
                                          | (_,_) -> failwith("WrongType"))
                            | _ -> failwith("WrongType"))
  | Fun(i, t1, t2, e) -> let tenv1 = bind tenv i t1 in
                          let tRet = teval e tenv1 in
                            if (tRet = t2) then TFun(t1,tRet)
                                         else failwith("WrongType")
  | FunCall(e1, e2) -> let f = teval e1 tenv in
                        (match f with
                        | TFun(t1,t2) -> if ((teval e2 tenv) = t1 ) then t2
                                                                    else failwith("WrongType")
                        | _ -> failwith("WrongType"))
  | LetRec(fname, funDef, letBody) -> (match funDef with
                                      | Fun(arg, t1, t2, body) -> let tenv1 = bind tenv fname (TFun(t1, t2)) in
                                                                    let t = teval funDef tenv1 in
                                                                      teval letBody (bind tenv fname t)
                                      | _ -> failwith ("WrongType"))
  | Dizionario(keys, vals) -> if (checkIntList vals) then TDict
                                                     else failwith("WrongType")
  | Insert(d, k, v) -> (match (teval d tenv) with
                        | TDict -> (match v with
                                    | EInt(n) -> TDict
                                    | _ -> failwith ("WrongType"))
                        | _ -> failwith("WrongType"))
  | Delete(d, k) -> (match (teval d tenv) with
                    | TDict -> TDict
                    | _ -> failwith("WrongType"))
  | HasKey(d, k) -> (match (teval d tenv) with
                    | TDict -> TBool
                    | _ -> failwith("WrongType"))
  | Filter(kl, d) -> (match (teval d tenv) with
                     | TDict -> TDict
                     | _ -> failwith("WrongType"))
  | Iterate(foo, d) -> (match (teval d tenv) with
                       | TDict -> (match (teval foo tenv) with
                                  | TFun(t1, t2) -> TDict
                                  | _ -> failwith("WrongType"))
                       | _ -> failwith("WrongType"))
  | Fold(foo, d) -> (match (teval d tenv) with
                    | TDict -> (match (teval foo tenv) with
                              | TFun(t1, t2) -> TInt 
                              | _ -> failwith("WrongType"))
                    | _ -> failwith("WrongType"));;



(* CASI DI TEST *)

(* variabili utili per i test e funzioni di supporto *)
let env0 = emptyenv Unbound;;
let funInc = Fun("x", TInt, TInt,(Add(Den("x"), EInt(1))));;

let printType t = match t with
| Unbound -> Printf.printf("Unbound\n");
| TInt -> Printf.printf("TInt\n");
| TBool -> Printf.printf("TBool\n");
| TFun(t1, t2) -> (match t1 with
                  | TInt -> (match t2 with
                            | TInt -> Printf.printf("TFun : (TInt -> TInt)\n");
                            | TBool -> Printf.printf("TFun : (TInt -> TBool)\n");
                            | _ -> failwith("WrongType"))
                  | TBool -> (match t2 with
                             | TInt -> Printf.printf("TFun : (TBool -> TInt)\n");
                             | TBool -> Printf.printf("TFun : (TBool -> TBool)\n");
                             | _ -> failwith("WrongType"))
                  | _ -> failwith("WrongType"))
| TDict -> Printf.printf("TDict\n");;


(* CASI DI TEST *)
Printf.printf "TEST DEL TYPE CHECKER\n";

Printf.printf "\nStampo il tipo di un dizionario:\n";
printType(teval (Dizionario(["mele"; "banane"; "arance"; "pere"], [EInt(430); EInt(312); EInt(525); EInt(217)])) env0);;

Printf.printf "\nStampo il tipo di un dizionario al quale inserisco una coppia chiave-valore:\n";
printType(teval (Insert(Dizionario(["mele"; "banane"; "arance"; "pere"], [EInt(430); EInt(312); EInt(525); EInt(217)]), "kiwi", EInt(85))) env0);;

Printf.printf "\nStampo il tipo di un dizionario al quale elimino una coppia chiave-valore:\n";
printType(teval (Delete(Dizionario(["mele"; "banane"; "arance"; "pere"], [EInt(430); EInt(312); EInt(525); EInt(217)]), "banane")) env0);;

Printf.printf "\nStampo il tipo del risultato della ricerca di una chiave in un dizionario:\n";
printType(teval (HasKey(Dizionario(["mele"; "banane"; "arance"; "pere"], [EInt(430); EInt(312); EInt(525); EInt(217)]), "banane")) env0);;

Printf.printf "\nStampo il tipo di un dizionario al quale seleziono solo alcune coppie chiave-valore:\n";
printType(teval (Filter(["mele"; "arance"; "pere"], (Dizionario(["mele"; "banane"; "arance"; "pere"], [EInt(430); EInt(312); EInt(525); EInt(217)])))) env0);;

Printf.printf "\nStampo il tipo di un dizionario al quale ho modificato i valori applicando una funzione:\n";
printType(teval (Iterate(funInc, Dizionario(["mele"; "banane"; "arance"; "pere"], [EInt(430); EInt(312); EInt(525); EInt(217)]))) env0);;

let fact = LetRec("fact", Fun("x", TInt, TInt,Ifthenelse(Eq(Den "x", EInt 0), EInt 1, Prod(Den "x", FunCall(Den "fact",(Sub(Den "x", EInt 1)))))), Fold(Den "fact", Dizionario(["dieci"; "tre"], [EInt(10); EInt(3)])));;
Printf.printf "\nStampo il tipo della Fold con una funzione ricorsiva applicata su un nuovo dizionario:\n";
printType(teval fact env0);;

Printf.printf "\nStampo il tipo del risultato dell'operazione logica AND:\n";
printType(teval (And(EBool(true), EBool(false))) env0);;

Printf.printf "\nStampo il tipo della funzione funInc:\n";
printType(teval funInc env0);;