Require Import Ensembles Bool.

Section Diaconescu.

Arguments In {U}.
Arguments Couple {U}.
Arguments Couple_l {U} {x} {y}.
Arguments Couple_r {U} {x} {y}.

Variable choice : forall {A : Type}, Ensemble A -> A.
Variable choice_prop : forall {A : Type} (x : Ensemble A), In x (choice A x).

Definition U (P : Prop) (x : bool) := x = true \/ P.
Definition V (P : Prop) (x : bool) := x = false \/ P.

Lemma P_imp_in_U : forall {P : Prop}, P -> forall (x : bool), In (U P) x.
Proof.
intuition.
unfold U, In.
intuition.
Qed.

Lemma P_imp_in_V : forall {P : Prop}, P -> forall (x : bool), In (V P) x.
Proof.
intuition.
unfold V, In.
intuition.
Qed.

Lemma P_imp_full : forall {P : Prop}, P -> U P = V P.
Proof.
intuition.
apply Extensionality_Ensembles.

unfold Same_set, Included.
intuition.
now (apply P_imp_in_V).
now (apply P_imp_in_U).
Qed.

Theorem diaconescu : forall (P : Prop), P \/ ~P.
Proof.
intuition.

pose proof choice_prop bool (U P) as fu.
pose proof choice_prop bool (V P) as fv.

inversion fu. inversion fv.

right.
intuition.
pose proof P_imp_full H1.
now (rewrite H2, H0 in H).

now left.
now left.
Qed.

End Diaconescu.
