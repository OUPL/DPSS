Require Import QArith.

Inductive Direction : Type :=
| dLeft : Direction
| dRight : Direction.

Definition changeDirection : Direction -> Direction :=
  fun d => match d with dLeft => dRight | dRight => dLeft end. 

Inductive directionFromSourceToTarget : Q -> Q -> Direction -> Prop :=
| ltDir :
    forall source target,
    source < target ->
      directionFromSourceToTarget source target dLeft
| gtDir :
    forall source target,
    target < source ->
      directionFromSourceToTarget source target dRight.

Lemma Direction_eq_dec : 
  forall d1 d2 : Direction, {d1 = d2} + {d1 <> d2}.
Proof.
  intros. destruct d1, d2; firstorder.
Qed.

Definition locationAfterTime : Q -> Direction -> Q -> Q -> Q :=
  fun location d speed time => 
  match d with
  | dLeft => location - (speed * time)
  | dRight => location + (speed * time)
  end.

Add Parametric Morphism : locationAfterTime with
  signature Qeq ==> eq ==> Qeq ==> Qeq ==> Qeq as locationAfterTime_mor.
Proof.
  intros. unfold locationAfterTime.
  destruct y0; rewrite H1, H0, H; reflexivity.
Qed.
(*
Lemma locationAfterTime_monotone_time_dLeft :
  forall location speed time1 time2,
    0 < speed ->
    time2 < time1 -> 
      locationAfterTime location dLeft speed time1 <
      locationAfterTime location dLeft speed time2.
Proof.
  intros. simpl locationAfterTime.
  apply Qlt_minus_iff.
  setoid_replace (_-_ location (speed * time2) + - _-_ location (speed * time1))
    with (speed * (time1 - time2)); try nsatz.
  apply Qle_lt_trans with (y := 0 * speed).
  apply Qle_lteq. right. nsatz.
  setoid_replace (_*_ speed (time1 - time2)) with
                 (_*_ (time1 + - time2) speed); try nsatz.
  apply Qmult_lt_compat_r; auto.
  rewrite <- Qlt_minus_iff. auto.
Qed.
*)