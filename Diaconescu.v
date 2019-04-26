Require Import Ensembles Bool.

Section Diaconescu.

Arguments In {U}.
Arguments Inhabited {U}.
Arguments Couple {U}.
Arguments Couple_l {U} {x} {y}.
Arguments Couple_r {U} {x} {y}.

Variable choice : forall {A : Set}, A -> Ensemble A -> A.
Variable choice_prop :
  forall {A : Set} (x : Ensemble A) (v : A), Inhabited x -> In x (choice A v x).

Definition U (P : Prop) (x : bool) := x = true \/ P.
Definition V (P : Prop) (x : bool) := x = false \/ P.

Lemma P_imp_in_U : forall {P : Prop}, P -> forall (x : bool), In (U P) x.
Proof.
intuition.
unfold U, In.
intuition.
Qed.

Lemma U_inhabited : forall {P : Prop}, Inhabited (U P).
Proof.
intuition.
exists true.
unfold U, In.
intuition.
Qed.

Lemma V_inhabited : forall {P : Prop}, Inhabited (V P).
Proof.
intuition.
exists false.
unfold V, In.
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
- now (apply P_imp_in_V).
- now (apply P_imp_in_U).
Qed.

Theorem diaconescu : forall (P : Prop), P \/ ~P.
Proof.
intuition.

pose proof choice_prop bool (U P) true U_inhabited as fu.
pose proof choice_prop bool (V P) true V_inhabited as fv.

inversion fu. inversion fv.

- right.
intros prf.
pose proof P_imp_full prf as eq_prf.
now (rewrite eq_prf, H0 in H).

- now left.
- now left.
Qed.

Require Import String.

Inductive conn (s : string) := blah.
Inductive open {s : string} (c : conn s) := bar.

Lemma lemma : exists (c : conn "google.com"), open c.
Proof.
pose proof diaconescu (exists (c : conn "google.com"), open c).
induction H.
intuition.
intuition.

Lemma ex_middle_neg : forall (P : Prop), ~(~(P \/ ~P)).
Proof.
intros.

unfold not.
intro prf.

cut (P -> False).

- intro assum.
exact (prf (or_intror assum)).

- intro assum.
exact (prf (or_introl assum)).
Qed.

End Diaconescu.
