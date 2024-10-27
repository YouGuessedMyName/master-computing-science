Require Export Coq.Logic.FinFun.
Require Import Lists.List.
Require Export Coq.Logic.ProofIrrelevance.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Relations.Relation_Definitions.

Import ListNotations.

Inductive I : Set.
Inductive O : Set.

Structure MealyMachine {Alphabet: Type} : Type :=
  new_mm {
  Q : Type;
  q0 : Q;
  delta : Q -> I -> Q;
  lambda: Q -> I -> O;  
}.



Inductive word (A : Set) : Set :=
  | eps : word A
  | nxt : A -> word A -> word A. 


Check eps I.
Check nxt I a (eps I).

Definition I_star := word I.
Definition O_star := word O.

(* Define general Mealy machine *)
Inductive Q : Set.
Definition delta := Q -> I -> Q.
Definition lambda := Q -> I -> O.

Fixpoint delta_star (q : Q) (df : delta) (sigma : word I) : Q := 
match sigma with
  | eps _ => q
  | nxt _ i sigma' => delta_star (df q i) df sigma'
end.

Fixpoint lambda_star (q : Q) (df : delta) (lf : lambda) (sigma : word I) : word O := 
match sigma with
  | eps _ => eps O
  | nxt _ i sigma' => nxt O (lf q i) (lambda_star q df lf sigma')
end.



Inductive QM : Q.
Definition deltaM := delta QM.
Definition lambdaM := lambda QM.
Parameter q0M : QM.

Check deltaM q0M.
Check lambdaM.




