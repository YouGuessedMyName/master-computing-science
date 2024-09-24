(* Intuitionistic logic is extended to classical logic
   by assuming a classical axiom. There are different
   possibilities for the choice of a classical axiom.
   In this practical work we show the logical equivalence
   of three different classical axioms. *)

(* The following are three classical axioms *)

Definition excluded_middle := forall A:Prop, A \/ ~A.
Definition peirce := forall A B:Prop, ((A -> B)-> A) -> A.
Definition double_negation := forall A:Prop, ~~A -> A.

(* To show that these are equivalent,
   we need to prove (at least) three implications.
   As an example, the implication
   excluded_middle implies peirce is given. *)

Lemma one : excluded_middle -> peirce.
Proof.
unfold excluded_middle.
unfold peirce.
unfold not.
intro EM.
intro A.
intro B.
elim (EM A).

intro x.
intro y.
assumption.

intro x.
intro y.
apply y.
intro z.
elimtype False.
apply x.
assumption.
Qed.

(* There is a new element in the syntax:
   a universal quantification over propositions.
   So in fact these formulas are second-order;
   we come back to that later in the course. *)

(* How to work with these universal quantifications ?
   With "intro" and "apply". Explanation by example:

   If the current goal is "forall A:Prop, A -> A",
   then by doing "intro A" the new goal is A -> A
   and a new hypothesis "A:Prop" appears.

   If the current goal is "C" and there is a hypothesis
   "x: forall A:Prop, B -> A"
   then by "apply x" the current goal is transformed into "B".
   The universally quantified A is instantiated by C.

   Now suppose that the current goal is "C" and
   there is a hypothesis "x: forall A B:Prop, B -> A".
   Then "apply x" does not work because from the
   current goal we can see how to instantiate A
   (namely with C) but not how to instantiate B.
   Therefore we should say "apply x with something."
   choosing something appropriately. *)

(* exercise; you need the "apply with". *)
Lemma two : peirce -> double_negation.
Proof.
unfold peirce.
unfold double_negation.
unfold not.
intro P.
intro x.
intro y.
apply P with False.
intro z.
exfalso.
apply y.
apply z.
Qed.

(* exercise *)
Lemma three : double_negation -> excluded_middle.
Proof.
unfold double_negation.
unfold excluded_middle.
unfold not.
intro DN.
intro x.
apply DN.
intro y.
apply y.
right.
intro z.
apply y.
left.
exact z.
Qed.

(* exercise *)
Lemma four : excluded_middle -> double_negation.
Proof.
unfold excluded_middle.
unfold double_negation.
unfold not.
intro EM.
intro x.
intro y.
destruct EM with x.
apply H.
exfalso.
apply y.
apply H.
Qed.

(* exercise *)
Lemma everything_related :
  excluded_middle -> forall A B : Prop , (A -> B) \/ (B -> A).
Proof.
unfold excluded_middle.
intro EM.
intros x y.
destruct EM with x.
right.
intro z.
apply H.
left.
intro t.
exfalso.
elim H.
apply t.
Qed.

Lemma de_morgan :
  excluded_middle -> forall A B : Prop , ~(~A/\~B) -> A\/B.
Proof.
unfold excluded_middle.
intro EM.
intros x y z.
destruct EM with x.
left.
exact H.
right.
destruct EM with y.
exact H0.
exfalso.
elim z.
split.
apply H.
apply H0.
Qed.

(* exercise
   note that this lemma is true intuitionistically *)
Lemma about_implication : forall A B : Prop , (~A \/ B) -> (A -> B).
Proof.
intros.
elim H.
intro x.
elim x.
exact H0.
intro y.
exact y.
Qed.

(* exercise
   for the converse of the previous lemma we need a classical axiom *)
Lemma classical_implication :
  excluded_middle -> forall A B : Prop , (A -> B) -> (~A \/ B).
Proof.
unfold excluded_middle.
intro EM.
intros.
destruct EM with A.
right.
apply H.
apply H0.
left.
apply H0.
Qed.

(* exercise *)
Lemma about_classical_implication :
  excluded_middle -> forall A B : Prop , ~B \/ (A ->B).
Proof.
unfold excluded_middle.
intros EM x y.
destruct EM with y.
right.
intro z.
exact H.
left.
exact H.
Qed.


