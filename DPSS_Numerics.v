Require Import QArith Qminmax Qabs QOrderedType.
Require Import Nsatz.

Definition Q_of_nat : nat -> Q := (fun n => inject_Z (Z_of_nat n)).

Section Distance.

  Definition qDistance (x y : Q) : Q :=
    Qabs (x-y).

  Lemma qDistance_Uniq : 
    forall x y, qDistance x y == 0 <-> x == y.
  Proof.
    intros. unfold qDistance.
    apply Qabs_case.
    - split; intros; nsatz.
    - split; intros; nsatz.
  Qed.

  Lemma qDistance_symm : 
    forall x y,
      qDistance x y == qDistance y x.
  Proof.
    intros. unfold qDistance.
    rewrite Qabs_Qminus. reflexivity.
  Qed.

  Add Parametric Morphism : qDistance with
    signature Qeq ==> Qeq ==> Qeq as qDistance_mor.
  Proof. intros. unfold qDistance. rewrite H, H0. reflexivity. Qed.

  Lemma qDistance_or : forall x y, 
    (x == y + (qDistance x y)) \/ (x == y - (qDistance x y)).
  Proof.
    unfold qDistance.
    intros. apply Qabs_case;
    intros; [left | right]; nsatz.
  Qed.

End Distance.

Section QInterval.

Record QInterval : Type :=
  mkInterval {
    upperBound : Q;
    lowerBound : Q;

    orderPf : lowerBound <= upperBound
  }.

Inductive inQInterval : Q -> QInterval -> Prop :=
| mkInQInterval :
    forall q QI,
      q <= (upperBound QI) ->
      (lowerBound QI) <= q ->
  inQInterval q QI.

Definition boundriesOfIntervalIntersection QInt1 QInt2 : Q * Q :=
    let UB := Qmin (upperBound QInt1) (lowerBound QInt2) in
    let LB := Qmax (lowerBound QInt1) (lowerBound QInt2) in
  (UB, LB).

  Definition intervalIntersection QInt1 QInt2 : option QInterval :=
    let boundries := boundriesOfIntervalIntersection QInt1 QInt2 in
    match Qlt_le_dec (fst boundries) (snd boundries) with
    | left _ => None
    | right pf => Some (mkInterval (fst boundries) (snd boundries) pf)
    end.

End QInterval.  