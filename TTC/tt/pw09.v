(* ************************************************* *)
(* prop2                                             *)
(* ************************************************* *)



(* the paradigmatic example corresponding to           *)
(* the polymorphic identity                            *)
(* we already print the inhabitant although we did not *)
(* yet discuss lambda2                                 *)

Lemma example1a : forall a:Prop, a->a.

Proof.
intro a.
intro x.
exact x.
Qed.
Print example1a.
(* \a:Prop. \x:a. x *)



Lemma example1b : forall a:Set, a -> a.

Proof.
intro a.
intro x.
exact x.
Qed.
Print example1b.
(* \a:Set. \x:a. x *)



(* another example from the course *)
Lemma example2: forall a:Prop, a -> (forall b:Prop, ((a -> b) -> b)).

Proof.
intro a.
intro x.
intro b.
intro y.
apply y.
exact x.
Qed.
Print example2.
(* \a:Prop. \x:a. \b:Prop. \y:a->b. (y x) *)


(* the following "lemma" is not valid *)
(*
Lemma example_wrong : forall a:Prop, a -> (forall b:Prop, b).

Proof.
intro a.
intro x.
intro b.
Abort.
*)

(* TODO *)
(* exercise 1 *)
(* give inhabitants of the following types: *)
(* forall a : Prop, a -> a *)
Definition exercise1a (a : Prop) : a -> a :=
  fun a : a => a.
Check exercise1a.
(* forall a b : Prop, (a -> b) -> a -> b *)
Definition exercise1b (a b : Prop) : (a -> b) -> a -> b :=
  fun (f : (a -> b)) (a : a) => f a.
Check exercise1b.
(* forall a : Prop, a -> forall b : Prop, (a -> b) ->  b*)
Definition exercise1c (a : Prop) (b : Prop) : (a -> b) ->  b :=
  fun f : (a -> b) => forall a : a, f a.
Check exercise1c.


(* exercises with negation *)

(* exercise 2 *)
Lemma exercise2 : forall a:Prop, a -> ~~a.
Proof.
intro a.
intro H.
unfold not.
intro I.
apply (I H).
Qed.

Lemma exercise3: forall a:Prop, ~~~a -> ~a.
Proof.
intros a H.
unfold not.
intro I.
apply H.
apply exercise2.
apply I.
Qed.

Lemma exercise4: forall a:Prop, ~~(~~a -> a).
Proof.
intro a.
intro H.
elim exercise2 with (~a).
unfold not.
intro I.
apply H.
intro J.
apply I.

unfold not.
intro I.
apply H.
intro J.
exfalso.
elim J.
unfold not.
apply I.
Qed.


(* exercises with full intuitionistic prop2 *)

Lemma exercise5 : forall a:Prop, (exists b:Prop, a) -> a.
Proof.
intro a.
intro H.
destruct H.
apply H.
Qed.

Lemma exercise6 : forall a:Prop, exists b:Prop, ((a -> b) \/ (b -> a)).
Proof.
intro a.
exists a.
left.
trivial.
Qed.



(* exercise with classical prop2 *)

Definition em:= forall a:Prop, a \/ ~a.

Lemma exercise7: em -> forall a b:Prop, ((a -> b) \/ (b -> a)).
Proof.
intro EM.
intro a.
intro b.
destruct EM with a.
right.
trivial.
left.
intro I.
elim H.
apply I.
Qed.

(* expressibility of prop2 *)
(* we will represent logical connectives in prop2 *)

(* definition of false *)
Definition new_false := forall a:Prop, a.

(* False implies new_false *)
Lemma exercise8 : False -> new_false.
Proof.
intro false.
exfalso.
apply false.
Qed.

(* new_false implies False *)
Lemma exercise9 : new_false -> False.
Proof.
unfold new_false.
intro nf.
apply nf.
Qed.

(* from new_false we can prove anything *)
Lemma exercise10 : forall a:Prop, new_false -> a.
Proof.
intros a nf.
apply nf.
Qed.


