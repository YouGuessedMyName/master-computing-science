(* ************************************************************** *)
Section pred1.

Variable Terms : Set.
Variable M : Terms.

(* predicates *)
Variable A : Prop.
Variable P : Terms -> Prop.
Variable Q : Terms -> Prop.
Variable R : Terms -> Terms -> Prop.

(* example *)
Theorem example0 : (forall x:Terms, (P x)) -> (P M).
Proof.
intro u.
apply u.
Qed.

Print example0.
(* \u: Pi x:Terms. Px. (u M) *)


(* example *)
Theorem example1 : forall x:Terms, (P x) -> (forall y:Terms, (P y) -> A) -> A.
Proof.
intro x.
intro h.
intro i.
apply i with x.
assumption.
Qed.

Print example1.
(* \x:Terms. \h:(P x). \i:(Pi y:Terms. Py -> A). (i x h) *)

(* example, see slide 35 of week 6 *)
Theorem example2 :
  (forall x : Terms , P x -> Q x)
  ->
  (forall x : Terms , P x)
  ->
  forall y : Terms , Q y.

Proof.
intro h.
intro i.
intro y.
apply h.
apply i.
Qed.
Print example2.
(* \h: (Pi x:Terms. Px -> Qx). \i: (Pi x:Terms Px). \y: Terms. h y (i y) *)

(* exercise 1: prove the lemma and inspect the proof term *)
Lemma one : (forall x : Terms, P x) -> P M.
Proof.
intro x.
apply x.
Qed.

Print one.

(* exercise 2: prove the lemma and inspect the proof term *)
Lemma two : (A -> forall x : Terms, P x) -> forall y : Terms, A -> P y.
Proof.
intros x y z.
apply x.
apply z.
Qed.

Print two.

(* exercise 3: prove the lemma and inspect the proof term *)
Lemma three : A -> forall x : Terms, A.
Proof.
intros x y.
apply x.
Qed.

Print three.

(* example, see slides 13-14-15 of week 7 *)
Definition AS :=
  forall x y : Terms, (R x y) -> ~(R y x).
Definition IR :=
  forall x:Terms, ~(R x x).

Theorem AS_implies_IR : AS -> IR.
Proof.
unfold AS.
unfold IR.
intro h.
intro x.
intro i.
apply h with x x.
  (* alternative: apply (h x x ) *)
exact i.
exact i.
Qed.
Print AS_implies_IR.

(* given *)
Definition reflif := forall x : Terms, (exists y : Terms, R x y) -> R x x.

(* exercise 4:
   define sym as the proposition stating that
   R is symmetric, that is,
   if x and y are related via R, then y and x are related via R *)
Definition sym := forall x y : Terms, 
    (R x y) -> (R y x)
  .

(* exercise 5:
   define trans as the proposition stating that
   R is transitive, that is,
   if x and y are related via R, and y and z are related via R,
   then x and z are related via R  *)
Definition trans := forall x y z: Terms, 
  (R x y) /\ (R y z) -> (R x z)
  .

(* exercise 6: prove the following Lemma *)
Lemma str : sym -> trans -> reflif.
Proof.
unfold sym.
unfold trans.
intro sym.
intro trans.
unfold reflif.
intro x.
intro H.
elim H.
intro z.
intro H0.
apply trans with z.
split.
apply H0.
apply sym.
apply H0.
Qed.

End pred1.

(* ************************************************************** *)

Section logical_framework.

(* we encode propositional logic
   source: webpage Herman Geuvers
   handbook article Henk Barendregt *)

(* prop representing the propositions is declared as a Set *)
Parameter prop : Set.

(* implication on prop is a binary operator *)
Parameter imp : prop -> prop -> prop.

(* we can use infix notation => for imp *)
Infix "=>" := imp (right associativity, at level 85).

(* T expresses if a proposion in prop is valid
   if (T p) is inhabited then p is valid
   if (T p) is not inhabited then p is not valid *)
Parameter T : prop -> Prop.

(* the variable imp_introduction models the introduction rule for imp *)
Parameter imp_introduction : forall p q : prop, (T p -> T q) -> T (p => q).

(* the variable imp_elimination models the elimination rule for imp *)
Parameter imp_elimination : forall p q : prop, T (p => q) -> T p -> T q.

(* exercise 7 : prove the following lemma *)
Lemma I : forall p : prop, T (p => p).
Proof.
intro p.
apply imp_introduction.
intro Tp.
apply Tp.
Qed.

(* exercise 8 : prove the following lemma *)
Lemma transitivity :
 forall p q r : prop, T (p => q) -> T (q => r) -> T (p => r).
Proof.
intros p q r.
intros p_q q_r.
apply imp_introduction.
intro Tp.
apply imp_elimination with q.
exact q_r.
apply imp_elimination with p.
exact p_q.
exact Tp.
Qed.

Parameter conjunction : prop -> prop -> prop.
Infix "X" := conjunction (no associativity, at level 90).

(* exercise 9 : define variables that model the introduction
   rule for conjuction on prop, and both elimination rules *)

Parameter conjunction_introduction : forall x y : prop, T x -> T y -> T (x X y)
  .

Parameter conjunction_elimination_l : forall x y : prop, T (x X y) -> T x
  .

Parameter conjunction_elimination_r : forall x y : prop, T (x X y) -> T x
  .

(* exercise 10: prove the following lemma *)
Lemma weak : forall a b c : prop, T (a => c) -> T ((a X b) => c).
Proof.
intros a b c.
intro a_c.
apply imp_introduction.
intro a_X_b.
apply imp_elimination with a.
apply a_c.
apply conjunction_elimination_l with b.
apply a_X_b.
Qed.


(* the remainder is not obligatory *)

(* bot represents falsum in prop *)
Parameter bot : prop.

(* not represents negation in prop *)
Definition not (p : prop) := p => bot.

(* not obligatory *)
(* exercise 11 : prove the following lemma *)
Lemma contrapositive : forall p q : prop, T (p => q) -> T (not q => not p).
Proof.
intros p q p_to_q.
apply imp_introduction.
unfold not.
intro not_q.
apply imp_introduction.
intro Tp.
apply imp_elimination with q.
apply not_q.
apply imp_elimination with p.
apply p_to_q.
apply Tp.
Qed.

End logical_framework.


