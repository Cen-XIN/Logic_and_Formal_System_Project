(********************************************************************************************************************)
(* We Work in a new module called Sandbox in % order not to conflict with existing definitions.                     *)
(********************************************************************************************************************)
Require Import Setoid.
Module Sandbox.

(********************************************************************************************************************)
(* We inductively define a type for Boolean expressions.                                                            *)
(* We cannot use 0 and 1, which are numbers and not valid constructors.                                             *)
(* We use T and F.                                                                                                  *)
(* Similarly, we use the type constructors and, or and not instead of x, + and overbar.                             *)
(********************************************************************************************************************)
Inductive Boolean : Set :=
| T: Boolean
| F: Boolean
| and : Boolean -> Boolean -> Boolean
| or : Boolean -> Boolean -> Boolean
| not : Boolean -> Boolean.

(********************************************************************************************************************)
(* We define the 10 laws of Boolean algebra  as axioms.                                                             *)
(********************************************************************************************************************)

Axiom Identity_and : 
forall (X:Boolean),
(and X T) = X.

Axiom Identity_or : 
forall (X:Boolean),
(or X F) = X.

Axiom Complementation_and : 
forall (X:Boolean),
(and X (not X)) = F.

Axiom Complementation_or : 
forall (X:Boolean),
(or X (not X)) = T.

Axiom Associativity_and : 
forall (X:Boolean), forall (Y:Boolean), forall (Z:Boolean),
(and X (and Y Z)) = (and (and X Y) Z).

Axiom Associativity_or : 
forall (X:Boolean), forall (Y:Boolean), forall (Z:Boolean),
(or X (or Y Z)) = (or (or X Y) Z).

Axiom Commutativity_and : 
forall (X:Boolean), forall (Y:Boolean),
(and X Y) = (and Y X).

Axiom Commutativity_or : 
forall (X:Boolean), forall (Y:Boolean),
(or X Y) = (or Y X).

Axiom Distributivity_and_or : 
forall (X:Boolean), forall (Y:Boolean), forall (Z:Boolean),
(and X (or Y Z)) = (or (and X Y) (and X Z)).

Axiom Distributivity_or_and : 
forall (X:Boolean), forall (Y:Boolean), forall (Z:Boolean),
(or X (and Y Z)) = (and (or X Y) (or X Z)).

(********************************************************************************************************************)
(* We can now prove other laws as theorems.                                                                          *)
(********************************************************************************************************************)

Theorem Idempotence_and: 
forall (X:Boolean),
(and X X) = X.
Proof.
intros.
rewrite <- (Identity_or (and X X)).
rewrite <- (Complementation_and X).
rewrite <- (Distributivity_and_or).
rewrite (Complementation_or).
rewrite (Identity_and).
reflexivity.
Qed.

(********************************************************************************************************************)
(* Prove the other laws given in the lecture.                                                                       *)
(********************************************************************************************************************)

Theorem Idempotence_or:
forall (X:Boolean),
(or X X) = X.

Proof.
intros.
rewrite <- (Identity_and (or X X)).
rewrite <- (Complementation_or X).
rewrite <- (Distributivity_or_and).
rewrite (Complementation_and).
rewrite (Identity_or).
reflexivity.
Qed.



Theorem Annihilator_and:
forall (X:Boolean),
(and X F) = F.

Proof.
intros.
rewrite <- (Complementation_and X).
rewrite (Associativity_and).
rewrite (Idempotence_and).
reflexivity.
Qed.


Theorem Annihilator_or:
forall (X:Boolean),
(or X T) = T.

Proof.
intros.
rewrite <- (Complementation_or X).
rewrite (Associativity_or).
rewrite (Idempotence_or).
reflexivity.
Qed.


Theorem Absorption_and:
forall (X:Boolean), forall (Y:Boolean),
(and X (or X Y)) = X.

Proof.
intros.
rewrite (Distributivity_and_or).
rewrite (Idempotence_and).
rewrite <- (Identity_and X) at 1.
rewrite <- (Distributivity_and_or).
rewrite <- (Commutativity_or Y).
rewrite (Annihilator_or Y).
rewrite (Identity_and X).
reflexivity.
Qed.


Theorem Absorption_or:
forall (X:Boolean), forall (Y:Boolean),
(or X (and X Y)) = X.

Proof.
intros.
rewrite (Distributivity_or_and).
rewrite (Idempotence_or).
rewrite <- (Identity_or X) at 1.
rewrite <- (Distributivity_or_and).
rewrite <- (Commutativity_and Y).
rewrite (Annihilator_and Y).
rewrite (Identity_or X).
reflexivity.
Qed.


Theorem Unicity_F:
forall (X:Boolean), forall (FF:Boolean),
(or X FF) = X /\ (and X (not X)) = FF -> FF=F.

Proof.
intros.
intuition.
rewrite <- (Complementation_and X).
rewrite H1.
reflexivity.
Qed.
