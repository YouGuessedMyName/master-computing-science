(* comments are written with parentheses and star *)
(* for the exercises: replace
   "parenthesis-star-exclamationmark-proof-star-parenthesis"
   by a proof. *)

(* an initial declaration *)
Parameter A B C : Prop.

(* example; the derivation is also in the course notes *)
Lemma example_one : A -> A.
Proof.
intro x.
assumption.
Qed.

Print example_one.

(* example; the derivation is also in the course notes *)
Lemma example_two : A -> B -> A.
Proof.
intro x.
intro y.
assumption.
Qed.

Print example_two.

(* example; the derivation is also in the course notes *)
Lemma example_three : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intro x.
intro y.
intro z.
apply x.
apply z.
apply y.
apply z.
Qed.

Print example_three.



(* the first exercises are concerned with
   minimal first-order propositional logic *)



(* exercise; see also the course notes *)
Lemma example : (A -> B) -> (C -> A) -> C -> B.
Proof.
intro x.
intro y.
intro z.
apply x.
apply y.
apply z.
Qed.

Print example.

(* exercise; see also the course notes; see also one_b *)
Lemma one_a : A -> A -> A.
Proof.
intro x.
intro y.
apply x.
Qed.

Print one_a.

(* exercise; see also the course notes
   give a proof that is different from the proof of one_a *)
Lemma one_b : A -> A -> A.
Proof.
intro x.
intro y.
apply y.
Qed.

Print one_b.

(* exercise; see also the course notes *)
Lemma permutation : (A -> B -> C) -> B -> A -> C.
Proof.
intro x.
intro y.
intro z.
apply x.
apply z.
apply y.
Qed.

Print permutation.

(* exercise; we did this one in class *)
Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
intro x.
apply x.
intro y.
apply y.
intro z.
apply x.
intro t.
apply z.
Qed.

Print weak_peirce.


(* now we extend minimal logic with falsum
   negation is defined: ~A = A -> False
   use the tactic "unfold" to unfold the definition *)



(* exercise *)
Lemma notfalse : ~ False.
Proof.
intro x.
apply x.
Qed.

Print notfalse.

(* exercise *)
Lemma exfalso : False -> A.
Proof.
intro x.
elim x.
Qed.

Print exfalso.

(* exercise; see also the course notes *)
Lemma contrapositive : (A -> B) -> ~ B -> ~ A.
Proof.
intro x.
intro y.
intro z.
apply y.
apply x.
assumption.
Qed.

Print contrapositive.

(* exercise; compare with weakpeirce *)
Lemma negations : ~~(~~A ->A).
Proof.
intro x.
apply x.
intro y.
elim y.
intro z.
apply x.
intro t.
assumption.
Qed.

Print negations.



(* now we move on to intuitionistic logic:
   conjunction /\ and disjunction \/ are added.
   in the exercises below we mainly practice the
   introduction and elimination rules for /\ and \/. *)



(* exercise *)
Lemma intro_and : A -> B -> A /\ B.
Proof.
intro x.
intro y.
split.
assumption.
assumption.
Qed.

Print intro_and.

(* exercise *)
Lemma elim_and : A /\ B -> A.
Proof.
(*intros [x y].
assumption.
destruct x.*)
intro x.
apply x.
Qed.

Print elim_and.

(* exercise *)
Lemma intro_or : A -> A \/ B.
Proof.
intro x.
left.
assumption.
Qed.

Print intro_or.

(* exercise *)
Lemma elim_or : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
intro x.
intro y.
intro z.
elim x.
intro t.
apply y.
apply t.
intro t.
apply z.
apply t.
Qed.

Print elim_or.

