Inductive nat : Prop := O : nat | S : nat -> nat.
Check nat_ind.
Check nat_rec.

Fixpoint pred (n : nat) {struct n} : nat :=
match n with
| O => O
| S m => m
end.

Definition pred2 (n : nat) :=
nat_ind nat
O
(fun m p => p) n.

Eval compute in (pred2 (S (S (S S (O)))).