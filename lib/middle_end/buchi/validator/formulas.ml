open MiddleParser.NcSyntax
open FrontParser.LTLSyntax
open HardyMisc.Utils

(* --------------------------- Atomic LTL --------------------------- *)

type 'a atomic_ltl = ALTL_True | ALTL_False | ALTL_A of 'a | ALTL_NotA of 'a

let atomic_ltl_to_bform = function
  | ALTL_False -> False
  | ALTL_True -> True
  | ALTL_A a -> Atom a
  | ALTL_NotA a -> Not (Atom a)

module AtomicSet = Set.Make (struct
  type t = string atomic_ltl

  let compare = Stdlib.compare
end)

let string_of_altl (string_of_pred : 'a -> string) = function
  | ALTL_A p -> string_of_pred p
  | ALTL_False -> "false"
  | ALTL_NotA p -> "~" ^ string_of_pred p
  | ALTL_True -> "true"

let print_atomicset fmt f =
  Format.fprintf fmt "%a"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt " , ")
       (fun fmt f -> Format.fprintf fmt "%s" (string_of_altl Fun.id f)))
    (AtomicSet.to_list f)

(* --------------------------- NNF LTL --------------------------- *)

(* only contains (negated) atomic formulas, next release, until, or, and  *)
type 'a nnf_ltl =
  | LTLM_True
  | LTLM_False
  | LTLM_A of 'a
  | LTLM_NotA of 'a
  | LTLM_Next of 'a nnf_ltl
  | LTLM_And of 'a nnf_ltl * 'a nnf_ltl
  | LTLM_Or of 'a nnf_ltl * 'a nnf_ltl
  | LTLM_Release of 'a nnf_ltl * 'a nnf_ltl
  | LTLM_Until of 'a nnf_ltl * 'a nnf_ltl

let nnf_of_atomic = function
  | ALTL_True -> LTLM_True
  | ALTL_False -> LTLM_False
  | ALTL_A a -> LTLM_A a
  | ALTL_NotA a -> LTLM_NotA a

module NNFSet = Set.Make (struct
  type t = string nnf_ltl

  let compare = Stdlib.compare
end)

let string_of_nnf (string_of_pred : 'a -> string) : 'a nnf_ltl -> string =
  let rec aux f =
    match f with
    | LTLM_True -> "true"
    | LTLM_False -> "false"
    | LTLM_A a -> string_of_pred a
    | LTLM_NotA na -> "not (" ^ string_of_pred na ^ ")"
    | LTLM_Until (f1, f2) ->
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) U (%s)" f1 f2
    | LTLM_Release (f1, f2) ->
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) R (%s)" f1 f2
    | LTLM_Or (f1, f2) ->
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) || (%s)" f1 f2
    | LTLM_And (f1, f2) ->
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) && (%s)" f1 f2
    | LTLM_Next f -> Format.sprintf "X (%s)" (aux f)
  in
  aux

let print_nnfset fmt f =
  Format.fprintf fmt "%a"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt " , ")
       (fun fmt f -> Format.fprintf fmt "%s" (string_of_nnf Fun.id f)))
    (NNFSet.to_list f)

(* --------------------------- Elementary LTL --------------------------- *)

type elementary_set = { atoms : AtomicSet.t; next_rooted : NNFSet.t }


let mk_empty_eset = { atoms = AtomicSet.empty; next_rooted = NNFSet.empty }
let mk_eltl_empty_next atoms = { mk_empty_eset with atoms }
let mk_eltl_empty_atoms next_rooted = { mk_empty_eset with next_rooted }

let nnf_of_eltl e =
  e.atoms |> AtomicSet.to_seq |> Seq.map nnf_of_atomic
  |> Fun.flip NNFSet.add_seq e.next_rooted

let print_eltl fmt f =
  Format.fprintf fmt "[ atoms: %a | next: %a ]" print_atomicset f.atoms
    print_nnfset f.next_rooted

module DisjunctSet = Set.Make (struct
  type t = elementary_set

  let compare = Stdlib.compare
end)

let print_disjunctset fmt (s : DisjunctSet.t) =
  Format.fprintf fmt "{@,%a@,}"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@,")
       (fun fmt f -> print_eltl fmt f))
    (DisjunctSet.to_list s)

let rec to_nnf (f : 'a ltl) : 'a nnf_ltl =
  let ltl_not x = mk_dummy_loc (LTL_Unary (LTL_StdUnary LNot, x)) in
  match f.value with
  | LTL_True -> LTLM_True
  | LTL_False -> LTLM_False
  | LTL_Atom p -> LTLM_A p
  | LTL_Unary (op, f) -> (
      match op with
      | Next -> LTLM_Next (to_nnf f)
      | Always -> LTLM_Release (LTLM_False, to_nnf f)
      | Eventually -> LTLM_Until (LTLM_True, to_nnf f)
      | LTL_StdUnary LNot -> (
          (* negation propagation *)
          match f.value with
          | LTL_Unary (LTL_StdUnary LNot, f) -> to_nnf f
          | LTL_True -> LTLM_False
          | LTL_False -> LTLM_True
          | LTL_Atom a -> LTLM_NotA a
          | LTL_Unary (Next, f) -> LTLM_Next (to_nnf (ltl_not f))
          | LTL_Unary (Always, f) ->
              to_nnf {f with value = LTL_Unary (Eventually, ltl_not f)}
          | LTL_Unary (Eventually, f) ->
              to_nnf {f with value = LTL_Unary (Always, ltl_not f)}
          | LTL_Binary (f1, bop, f2) -> (
              match bop with
              | Release -> LTLM_Release (to_nnf f1, to_nnf f2)
              | Until -> LTLM_Until (to_nnf f1, to_nnf f2)
              | WeakUntil ->
                  let f2 = to_nnf f2 in
                  LTLM_Release (f2, LTLM_Or (f2, to_nnf f1))
              | StrongRelease ->
                  let f2 = to_nnf f2 in
                  LTLM_Until (f2, LTLM_Or (f2, to_nnf f1))
              | LTL_StdBinary LAnd ->
                  to_nnf
                    { f with value = LTL_Binary (ltl_not f1, LTL_StdBinary LOr, ltl_not f2);
                    }
              | LTL_StdBinary LOr ->
                  to_nnf
                    { f with
                      value =  LTL_Binary (ltl_not f1, LTL_StdBinary LAnd, ltl_not f2);
                    }
              | LTL_StdBinary Equiv ->
                 let f1 = to_nnf f1
                  and not_f1 = to_nnf (ltl_not f1)
                  and f2 = to_nnf f2
                  and not_f2 = to_nnf (ltl_not f2) in
                  LTLM_Or (LTLM_And (f1, not_f2), LTLM_And (not_f1, f2))
              | LTL_StdBinary Arrow -> LTLM_And (to_nnf f1, to_nnf (ltl_not f2)))))
      | LTL_Binary (f1, bop, f2) -> (
          match bop with
          | Release -> LTLM_Release (to_nnf f1, to_nnf f2)
          | Until -> LTLM_Until (to_nnf f1, to_nnf f2)
          | WeakUntil ->
              let f2 = to_nnf f2 in
              LTLM_Release (f2, LTLM_Or (f2, to_nnf f1))
          | StrongRelease ->
              let f2 = to_nnf f2 in
              LTLM_Until (f2, LTLM_Or (f2, to_nnf f1))
          | LTL_StdBinary op -> (
              match op with
              | LAnd -> LTLM_And (to_nnf f1, to_nnf f2)
              | LOr -> LTLM_Or (to_nnf f1, to_nnf f2)
              | Equiv ->
                  let f1 = to_nnf f1
                  and not_f1 = to_nnf (ltl_not f1)
                  and f2 = to_nnf f2
                  and not_f2 = to_nnf (ltl_not f2) in
                  LTLM_And (LTLM_Or (f1, not_f2), LTLM_Or (not_f1, f2))
              | Arrow ->
                  let f1 = to_nnf (ltl_not f1) in
                  LTLM_Or (f1, to_nnf f2)
              ))

let rec apply_identities : 'a nnf_ltl -> 'a nnf_ltl = function
  | (LTLM_True | LTLM_False | LTLM_A _ | LTLM_NotA _) as f -> f
  | LTLM_Next f -> LTLM_Next f (* leave it as is *)
  | LTLM_Release (f1, f2) as r ->
      (* f2 /\ (f1 \/ X (f1 U f2)) *)
      let f1 = apply_identities f1 and f2 = apply_identities f2 in
      LTLM_And (f2, LTLM_Or (f1, LTLM_Next r))
  | LTLM_Until (f1, f2) as u ->
      let f1 = apply_identities f1 and f2 = apply_identities f2 in
      (* f2 \/ (f1 /\ X (f1 U f2)) *)
      LTLM_Or (f2, LTLM_And (f1, LTLM_Next u))
  | LTLM_And (f1, f2) ->
      let f1 = apply_identities f1 and f2 = apply_identities f2 in
      LTLM_And (f1, f2)
  | LTLM_Or (f1, f2) ->
      let f1 = apply_identities f1 and f2 = apply_identities f2 in
      LTLM_Or (f1, f2)

(* let rec distribute_and : 'a nnf_ltl -> 'a nnf_ltl = function
  | ( LTLM_True | LTLM_False | LTLM_A _ | LTLM_NotA _
    | LTLM_Next _ (* no need to do anything for X-rooted subformulas *) ) as f
    ->
      f
  | LTLM_Release _ | LTLM_Until _ ->
      (* we applied identities before distributing : release and until formulas must be encapsulated
         by the next operator we do not recurse on, so these formulas cannot be reached *)
      assert false
  | LTLM_And (f3, LTLM_Or (f1, f2)) | LTLM_And (LTLM_Or (f1, f2), f3) ->
      let f1 = distribute_and f1
      and f2 = distribute_and f2
      and f3 = distribute_and f3 in
      LTLM_Or (LTLM_And (f1, f3), LTLM_And (f2, f3))
  | LTLM_And (f1, f2) -> LTLM_And (distribute_and f1, distribute_and f2)
  | LTLM_Or (f1, f2) -> LTLM_Or (distribute_and f1, distribute_and f2) *)

(* let fixpoint (stable : 'a -> 'a -> bool) (f : 'a -> 'a) : 'a -> 'a =
  let rec aux x =
    let x' = f x in
    if stable x' x then x' else aux x'
  in
  aux

(* fixpoint2 first wait for f1 stabilization before running f2 and checking for stabilization *)
let fixpoint2 (stable : 'a -> 'a -> bool) f1 f2 =
  fixpoint stable (fixpoint stable f1 >> f2) *)


let build_ecovering (conj : NNFSet.t) (bform_sat: string bform -> bool)=
  let rec to_dnf = function
    | LTLM_True ->
        ALTL_True |> AtomicSet.singleton |> mk_eltl_empty_next
        |> DisjunctSet.singleton
    | LTLM_False ->
        ALTL_False |> AtomicSet.singleton |> mk_eltl_empty_next
        |> DisjunctSet.singleton
    | LTLM_A a ->
        ALTL_A a |> AtomicSet.singleton |> mk_eltl_empty_next
        |> DisjunctSet.singleton
    | LTLM_NotA na ->
        ALTL_NotA na |> AtomicSet.singleton |> mk_eltl_empty_next
        |> DisjunctSet.singleton
    | LTLM_Next f ->
        f |> NNFSet.singleton |> mk_eltl_empty_atoms |> DisjunctSet.singleton
    | LTLM_And (f1, f2) ->
        (* fixme: ugly, use params to propagate ? *)
        let f1 = to_dnf f1 and f2 = to_dnf f2 in
        DisjunctSet.(
          fold
            (fun conj1 disj ->
              union disj
                (map
                   (fun conj2 ->
                     {
                       atoms = AtomicSet.union conj1.atoms conj2.atoms;
                       next_rooted =
                         NNFSet.union conj1.next_rooted conj2.next_rooted;
                     })
                   f2))
            f1 empty)
    | LTLM_Or (f1, f2) -> DisjunctSet.union (to_dnf f1) (to_dnf f2)
    | LTLM_Release (_, _) | LTLM_Until (_, _) -> assert false
  in

  let rec aux ((opened, closed) : NNFSet.t * DisjunctSet.t) =
    match NNFSet.choose_opt opened with
    | None -> closed
    | Some f ->
        let dnf = (apply_identities >> to_dnf) f in
        
        let eset_sat e = fold_mjoin atomic_ltl_to_bform
              (fun x y -> And (x, y))
              True
              (AtomicSet.to_list e.atoms) |> bform_sat
        in
        (* discard inconsistent esets *)
        let dnf = DisjunctSet.filter eset_sat dnf in


        let dnf = 
         if DisjunctSet.is_empty dnf then
          (* if there is no consistent eset, return false 
            (if left empty, the covering would be considered true)
          *)
          DisjunctSet.singleton (mk_eltl_empty_next (AtomicSet.singleton ALTL_False))

        else 
          if DisjunctSet.exists
                (fun e ->
                  NNFSet.is_empty e.next_rooted
                  && e.atoms = AtomicSet.singleton ALTL_True)
                dnf
            then
          (* if the atoms of an elementary set with no X-formulas form a tautology,
              there is nothing to add (the 'conj' formulas together form a tautology)
          *)
          DisjunctSet.empty
        else 
           (* empty next_rooted are replaced by the singleton LTLM_True so that after building the covering, 
              checking an eset with no next-time formula will result in checking for a universal path *)
          DisjunctSet.map NNFSet.(fun e -> 
            if is_empty e.next_rooted then {e with next_rooted = NNFSet.singleton LTLM_True}else e
          ) dnf
        in
        aux (NNFSet.remove f opened, DisjunctSet.union dnf closed)
  in
  Format.printf "building covering for: [%a]@," print_nnfset conj;
  aux (conj, DisjunctSet.empty)
