(** 
    This file outlines a couple of equivalence classes and sets up the
    appropriate morphisms we use later in the development.

    Author: Sam Merten
**)

Require Import QArith Qminmax Qabs QOrderedType.
Require Import Omega Nsatz.
Require Import List Setoid SetoidList Permutation SetoidPermutation.
Require Import Coq.Classes.RelationClasses.
Require Import ProofIrrelevance.

(* This extends an equivalence realtion over (A : Type) to (option A) **)
Section Options.
  Variable A : Type.
  Variable Eq_opt_base : A -> A -> Prop.
  Variable EqA_equiv : Equivalence Eq_opt_base.

  Inductive Eq_opt : option A -> option A -> Prop :=
  | Eq_opt_None : Eq_opt None None
  | Eq_opt_Some : forall a1 a2, Eq_opt_base a1 a2 -> Eq_opt (Some a1) (Some a2).

  Lemma Eq_opt_refl : reflexive _ Eq_opt.
  Proof.
    unfold reflexive. intros. destruct x; constructor.
    apply EqA_equiv.
  Qed.

  Lemma Eq_opt_symm : symmetric _ Eq_opt.
  Proof.  
    unfold symmetric. intros.
    inversion H; constructor; subst; firstorder.
  Qed. 

  Lemma Eq_opt_trans : transitive _ Eq_opt.
  Proof.
    unfold transitive. intros.
    inversion H; inversion H0; try congruence.
    constructor. subst. inversion H5. subst.
    etransitivity; eauto.
  Qed.

  Lemma Eq_opt_equiv : Equivalence Eq_opt.
  Proof.
    constructor.
    - apply Eq_opt_refl.
    - apply Eq_opt_symm.
    - apply Eq_opt_trans.
  Qed.

End Options.

(** Extensional equality over functions as an equivalence class **)
Section Functions.

  Section OneArity_FunctionalEq.
    Variables A B : Type.
    Variable EqB : B -> B -> Prop.
    Variable EqB_equiv : Equivalence EqB.

    Inductive EqF : (A -> B) -> (A -> B) -> Prop :=
    | mkEqF :
        forall f1 f2,
          (forall a, EqB (f1 a) (f2 a)) -> EqF f1 f2.

    Lemma EqF_refl : reflexive _ EqF.
    Proof. constructor. intros. firstorder. Qed.

    Lemma EqF_symm : symmetric _ EqF.
    Proof. constructor. intros. inversion H. firstorder. Qed.

    Lemma EqF_trans : transitive _ EqF.
    Proof.
      constructor. inversion H. inversion H0. intros. etransitivity; eauto.
    Qed.

    Lemma EqF_equiv : Equivalence EqF.
    Proof.
      constructor.
      - apply EqF_refl.
      - apply EqF_symm.
      - apply EqF_trans.
    Qed.

  End OneArity_FunctionalEq.

  Variables A B1 B2 C : Type.

  Variable EqC : C -> C -> Prop.
  Variable EqC_equiv : Equivalence EqC.

  Definition EqF2 : (A -> B1 -> C) -> (A -> B1 -> C) -> Prop :=
    (EqF _ _ (EqF _ _ EqC)).

  Lemma EqF2_equiv : Equivalence EqF2.
  Proof. do 2 apply EqF_equiv. auto. Qed.

End Functions.

  (** Extending Qeq to work over (option Q) **)
Section QOpt.

  Definition Qeq_opt : option Q -> option Q -> Prop :=
    Eq_opt _ Qeq.

  Lemma Qeq_opt_refl : reflexive _ Qeq_opt.
  Proof. apply Eq_opt_refl. apply Q_Setoid. Qed.

  Lemma Qeq_opt_symm : symmetric _ Qeq_opt.
  Proof. apply Eq_opt_symm. apply Q_Setoid. Qed.

  Lemma Qeq_opt_trans : transitive _ Qeq_opt.
  Proof. apply Eq_opt_trans. apply Q_Setoid. Qed.

  Add Parametric Relation : (option Q) (Qeq_opt)
    reflexivity proved by Qeq_opt_refl
    symmetry proved by Qeq_opt_symm
    transitivity proved by Qeq_opt_trans
    as Qeq_opt_rel.
End QOpt.
