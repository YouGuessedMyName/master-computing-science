(* Inductive nat : Set := O : nat | S : nat -> nat. *)
Check nat_ind.
Check nat_rec.

Fixpoint pred (n : nat) {struct n} : nat :=
match n with
| O => O
| S m => m
end.

Definition pred2 (n : nat) :=
nat_rec (fun n : nat => nat)
O
(fun m p => m) n.

Print pred2.

Inductive le (n : nat) : nat -> Prop :=
le_n : le n n
| le_S : forall m : nat, le n m -> le n (S m).

Check le_ind.

Inductive and (A B : Set) : Set :=
conj : A -> B -> and A B.

Check and_ind.

Check (le_S 2 3 (
le_S 2 2 (
le_n 2))).

Eval compute in (pred2 (S (S O))).


Inductive nattree : Set :=
| node : nattree -> nattree -> nattree
| leaf : nat -> nattree.

Fixpoint nattree_sum (t : nattree) {struct t} : nat :=
match t with
| node t1 t2 => plus (nattree_sum t1) (nattree_sum t2)
| leaf n => n
end.

Check nattree_rec.

Definition nattree_sum_rec (t : nattree) : nat :=
nattree_rec
(fun t : nattree => nat)
(fun t1 n1 t2 n2 => plus n1 n2)
(fun n => n) t.

Inductive polytree (A : Set) : Set :=
| polynode : polytree A -> polytree A -> polytree A
| polyleaf : A -> polytree A.

(*
polytree_ind
  : forall A : Set, forall P : polytree A -> Prop,
    (forall t1 polytree A, P t1 ->
     forall t2 polytree A, P t2 ->
        P (polynode A t1 t2)) ->
    (forall a : A, P (polyleaf A a)) ->
    forall t : polytree A, P t.
*)

