(* initial declaration *)
Parameter A B C D : Prop.



(* The first set of exercises are concerned with minimal logic.
   The question is to prove the lemma's
   and to print (and read) the lambda term corresponding
   to the proof. *)

(* NB: if the name of a bound variable does not matter
   then Coq may print "_" instead of for instance "x". *)

(* first an example *)
Lemma example : (A -> B) -> (B -> C) -> A -> C.
Proof.
intros x y z.
apply y.
apply x.
exact z.
Qed.

Print example.
(* fun (x : A -> B) (y : B -> C) (z : A) => y (x z) *)

(* exercise one_a *)
Lemma one_a : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
intros.
apply H1.
apply H0.
Qed.

Print one_a.

(* exercise one_b *)
Lemma one_b : ((A -> B) -> (C ->D)) -> C -> B -> D.
Proof.
intros.
apply H.
intros.
apply H1.
apply H0.
Qed.

Print one_b.

(* exercise one_c *)
Lemma one_c : (A -> B) -> (A -> C) -> A -> B -> C.
Proof.
intros.
apply H0.
intros.
apply H1.
Qed.

Print one_c.



(* The second set of exercises is concerned with negation.
   Recall that ~A is defined as A -> False.
   The negation in the goal can be unfolded by "unfold not.". *)

(* NB: a lemma Name that is proved earlier can be used
   by "apply Name."
   NB: if you want to proceed upwards using the elimination
   rule for false, then the Coq tactic is "elimtype False." *)

(* exercise two_a; see Chapter 1 of the course notes
   NB: the converse is not true intuitionistically *)
Lemma AnotnotA : A -> ~ ~ A .
Proof.
intros.
intro x.
apply x.
apply H.
Qed.

(* exercise two_b; see Chapter 1 of the course notes *)
Lemma notnotnot : ~ ~ ~ A -> ~ A.
Proof.
intros.
intro x.
apply H.
apply AnotnotA.
apply x.
Qed.

(* exercise two_c; see Chapter 1 of the course notes *)
Lemma herman : ~ ~ (~ ~ A -> A).
Proof.
unfold not.
intro x.
apply x.
intro y.
exfalso.
apply y.
intro z.
apply x.
intro t.
apply z.
Qed.

Print herman.



(* The third set of exercises consist of incomplete
   lambda terms. The question is to add types in such
   a way that a typable lambda term is obtained.
   Use "Check <term>." to see whether it is ok. *)

(* example:
   question:  Check fun (x:?) => x.
   answer:   Check fun (x:A) => x. *)

(* exercises: *)

Check fun (x : A -> A -> A) (y : A) (z : A) => x y z.
Check fun (x : B -> C) (y : A -> B) (z : A) => x (y z).
Check fun (x : A -> A) (y : A) => x y.
Check fun (x : A -> B -> C) (y : B) (z : A) => x z y .





(* In the fourth set of exercises, a type is given and
   the question is to define (using "Definition") an
   inhabitant of that type.
   You can define an inhabitant with or without using Coq.
   Use "Check <name>." to see whether it is correct. *)

(* example:
   question: A -> A
   answer: Definition example := fun (x :A) => x .
           Check example.                           *)

(* exercises *)

(* four_a: (A -> B) -> (A -> C) -> A -> B -> C *)
Definition four_a := 
  fun (ab :A -> B) (ac :A -> C) (a:A) (b:B) => ac a.

Check four_a.


(* four_b : A -> A -> A *)
Definition four_b := (*! term *)
  fun (x:A) (y:A) => x.

Check four_b.

(* four_c : A -> A -> A  but different from four_b*)
Definition four_c := (*! term *)
  fun (x:A) (y:A) => y.

Check four_c.

(* four_d : A -> B -> A *)
Definition four_d :=
  fun (x:A) (y:B) => x.

Check four_d.

(* four_e : (A -> A) -> A -> A *)
Definition four_e := (*! term *)
  fun (aa: A->A) (x:A) => x.

Check four_e.

(* four_f : (A -> A) -> A -> A but different from four_e *)
Definition four_f :=
  fun (aa: A->A) (x:A) => aa x.

Check four_f.

(* four_g : (A -> A -> B) -> A -> B *)
Definition four_g :=
  fun (aab: A->A->B) (a: A) => aab a a.

Check four_g.


