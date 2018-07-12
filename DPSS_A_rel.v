(** 
    This file provides a relational description of an
    environment executing DPSS -- Algorithm A.


    Author: Sam Merten
**)


Require Import QArith Qminmax Qabs QOrderedType.
Require Import Omega Nsatz.
Require Import Setoid List SetoidList Permutation SetoidPermutation.
Require Import Coq.Classes.RelationClasses.
Require Import ProofIrrelevance.

Require Import ExtendedEqualities.
Require Import DPSS_Primitives DPSS.DPSS_Numerics.

Existing Instance Qeq_opt_rel.

(** Definition of agents acting in the environment **)
Record simAgent : Type :=
  mkRealAgent {
    sHeading : Direction; (* The direction of the agents movement *)
    sLocation : Q; (* The agent's current location *)
    sDestination : option Q; (* Where the agent ends its escort *)
    sAgentID : nat;
  }.

(** Begin:
      setoid equality for simAgents and morphisms for record fields **)
Inductive simAgentEQ : simAgent -> simAgent -> Prop :=
  mkSA_EQ :
    forall a1 a2, sHeading a1 = sHeading a2 ->
                  sLocation a1 == sLocation a2 ->
                  sAgentID a1 = sAgentID a2 ->
                  Qeq_opt (sDestination a1) (sDestination a2) ->
    simAgentEQ a1 a2.


Lemma simAgentEQ_refl : reflexive _ simAgentEQ.
Proof. constructor; firstorder. Qed.

Lemma simAgentEQ_symm : symmetric _ simAgentEQ.
Proof. constructor; inversion H; firstorder. Qed.

Lemma simAgentEQ_trans :transitive _ simAgentEQ.
Proof.
  constructor; inversion H; inversion H0; 
  etransitivity; eauto.
Qed.

Lemma simAgentEQ_equiv : Equivalence simAgentEQ.
Proof.
  constructor.
  - apply simAgentEQ_refl. 
  - apply simAgentEQ_symm.
  - apply simAgentEQ_trans.
Qed.

Add Parametric Relation : (simAgent) (simAgentEQ)
  reflexivity proved by simAgentEQ_refl
  symmetry proved by simAgentEQ_symm
  transitivity proved by simAgentEQ_trans
  as simAgentEQ_rel.

Add Parametric Morphism : sHeading with
  signature simAgentEQ ==> eq as sHeading_mor.
Proof.
  intros. inversion H. auto.
Qed.

Add Parametric Morphism : sLocation with
  signature simAgentEQ ==> Qeq as sLocation_mor.
Proof.
  intros. inversion H. auto.
Qed.

Add Parametric Morphism : sDestination with
  signature simAgentEQ ==> Qeq_opt as sDestination_mor.
Proof.
  intros. inversion H. firstorder.
Qed.

Add Parametric Morphism : sAgentID with
  signature simAgentEQ ==> eq as sAgentID_mor.
Proof.
  intros. inversion H. auto.
Qed.
(** End:
      setoid equality for simAgents and morphisms for record fields **)


(** A definition of the environment in the simulation **)
Inductive simEnv :=
  mkRealEnv {
    sNumAgents : nat;
    sAgents : forall (n : nat), (n < sNumAgents)%nat -> simAgent;
    sPerimLength : Q;
    sSpeed : Q;
    sTime : Q
}.

(** Begin:
      setoid equality for simEnvs and morphisms for record fields **)
Inductive simEnvEQ : simEnv -> simEnv -> Prop :=
  mkSE_EQ :
    forall e1 e2, sNumAgents e1 = sNumAgents e2 ->
                  (forall n pf1 pf2,
                    simAgentEQ (sAgents e1 n pf1) (sAgents e2 n pf2)) ->
                  sPerimLength e1 == sPerimLength e2 ->
                  sSpeed e1 == sSpeed e2 ->
                  sTime e1 == sTime e2 -> 
    simEnvEQ e1 e2.

Lemma simEnvEQ_refl : reflexive _ simEnvEQ.
Proof.
  constructor; intros; try (replace pf1 with pf2); firstorder.
  apply proof_irrelevance.
Qed.

Lemma simEnvEQ_symm : symmetric _ simEnvEQ.
Proof.
  constructor; inversion H; intros; firstorder.
  symmetry. apply H1.
Qed.

Lemma simEnvEQ_trans : transitive _ simEnvEQ.
Proof.
  constructor; inversion H; inversion H0; intros; firstorder;
  etransitivity; eauto. Unshelve. firstorder.
Qed.

Lemma simEnvEQ_equiv : Equivalence simEnvEQ.
Proof.
  constructor.
  - apply simEnvEQ_refl.
  - apply simEnvEQ_symm.
  - apply simEnvEQ_trans.
Qed.

Add Parametric Relation : (simEnv) (simEnvEQ)
  reflexivity proved by simEnvEQ_refl
  symmetry proved by simEnvEQ_symm
  transitivity proved by simEnvEQ_trans
  as simEnvEQ_rel.

Add Parametric Morphism : sNumAgents with 
  signature simEnvEQ ==> eq as sNumAgents_mor.
Proof. intros. inversion H. firstorder. Qed.

Add Parametric Morphism : sPerimLength with
  signature simEnvEQ ==> Qeq as sPerimLenght_mor.
Proof. intros. inversion H. firstorder. Qed.

Add Parametric Morphism : sSpeed with
  signature simEnvEQ ==> Qeq as sSpeed_mor.
Proof. intros. inversion H. firstorder. Qed.

Add Parametric Morphism : sTime with
  signature simEnvEQ ==> Qeq as sTime_mor.
Proof. intros. inversion H. firstorder. Qed.

(*
  Because of the dependecy of the proof term in sAgents,
    building a morphism for this term is obnoxious. Instead,
    we'll just do the rewriting manually.
*) 
Lemma sAgents_mor : 
  forall e1 e2 n1 n2 pf1 pf2,
    simEnvEQ e1 e2 ->
    n1 = n2 ->
    simAgentEQ (sAgents e1 n1 pf1) (sAgents e2 n2 pf2).
Proof. intros. subst. inversion H; subst. apply H1. Qed.
(** End:
      setoid equality for simEnvs and morphisms for record fields **)



(* The perimeter boundries for agents *)  
Definition agentUpperPatrolRange
  (n : nat) (E : simEnv) (pf : (n < sNumAgents E)%nat) : Q :=
  (1 + (Q_of_nat n)) * (sPerimLength E) / (Q_of_nat (sNumAgents E)).

Definition agentLowerPatrolRange
  (n : nat) (E : simEnv) (pf : (n < sNumAgents E)%nat) : Q :=
  ((Q_of_nat n)) * (sPerimLength E) / (Q_of_nat (sNumAgents E)).

Lemma agentPatrolRange_order :  
  forall n E pf1 pf2,
    0 < sPerimLength E ->
    0 < Q_of_nat (sNumAgents E) ->
    agentLowerPatrolRange n E pf1 < agentUpperPatrolRange n E pf2.
Proof.
  intros. unfold agentLowerPatrolRange, agentUpperPatrolRange.
  apply Qlt_shift_div_l. auto. field_simplify.
  rewrite Qlt_minus_iff. field_simplify in H. field_simplify. auto.
  - intros H1. rewrite H1 in H0. inversion H0.
Qed.

Program Definition agentPatrolRange
  n E pf
  (pf_perimlength : 0 < sPerimLength E)
  (pf_agentnum : 0 < Q_of_nat (sNumAgents E))  
: QInterval :=
    mkInterval (agentUpperPatrolRange n E pf)
              (agentLowerPatrolRange n E pf)
             _.
Next Obligation. apply Qlt_le_weak. apply agentPatrolRange_order; auto. Qed.

(* Again, the propositions make this obnoxious to do automatically *)
Lemma agentUpperPatrolRange_mor :
  forall e1 e2 n1 n2 pf1 pf2,
    simEnvEQ e1 e2 ->
    (n1 = n2) ->
      Qeq (agentUpperPatrolRange n1 e1 pf1) (agentUpperPatrolRange n2 e2 pf2).
Proof.
  intros. unfold agentUpperPatrolRange. rewrite H, H0. firstorder.
Qed.

Lemma agentLowerPatrolRange_mor :
  forall e1 e2 n1 n2 pf1 pf2,
    simEnvEQ e1 e2 ->
    (n1 = n2) ->
      Qeq (agentLowerPatrolRange n1 e1 pf1) (agentLowerPatrolRange n2 e2 pf2).
Proof.
  intros. unfold agentLowerPatrolRange. rewrite H, H0. firstorder.
Qed.

(** Properties of  a valid environment **)
Inductive sNumAgents_Pos_inv : simEnv -> Prop :=
| mkNumAgents_Pos_inv : 
    forall E, (O < sNumAgents E)%nat -> sNumAgents_Pos_inv E.

Inductive sPerimLength_Pos_inv : simEnv -> Prop :=
| mkPerimLength_Pos_inv :
    forall E, (0 < sPerimLength E) -> sPerimLength_Pos_inv E.

Inductive sSpeed_Positive_inv : simEnv -> Prop :=
| mkSpeed_Positive_inv :
    forall E, 0 < sSpeed E -> sSpeed_Positive_inv E.

Inductive sAgents_InPerim_inv : simEnv -> Prop :=
| mkAgents_InPerim_inv :
    forall E,
    (forall n (pf : (n < sNumAgents E)%nat),
        0 <= (sLocation (sAgents E n pf)) <= sPerimLength E) ->
      sAgents_InPerim_inv E.

Inductive sAgents_Ordered_inv : simEnv -> Prop :=
| mkAgents_Ordered_inv :
    forall E,
    ( forall n1 n2
        (pf1 : (n1 < sNumAgents E)%nat)
        (pf2 : (n2 < sNumAgents E)%nat)
        (pf3 : (n1 < n2)%nat),
          (sLocation (sAgents E n1 pf1)) <= (sLocation (sAgents E n2 pf2))) ->
  sAgents_Ordered_inv E.

Inductive sAgents_heading_towards_dest_inv : simEnv -> Prop := 
| mkAgents_heading_towards_dest_inv :
    forall E,
    ( forall n
        (pf : (n < sNumAgents E)%nat) d,
          sDestination (sAgents E n pf) =  Some d ->
            directionFromSourceToTarget
              (sLocation (sAgents E n pf))
              d
              (sHeading ((sAgents E n pf)))) ->
    sAgents_heading_towards_dest_inv E.

Inductive sAgents_dest_in_perim_inv : simEnv -> Prop :=
| mkAgents_dest_in_perim_inv :
    forall E, 
      ( forall n
          (pf : (n < sNumAgents E)%nat) d,
          Qeq_opt (sDestination (sAgents E n pf)) (Some d) ->
            0 <= d <= sPerimLength E) ->
  sAgents_dest_in_perim_inv E.

Inductive sAgents_ID_match_inv : simEnv -> Prop :=
| mkAgents_ID_match_inv :
    forall E,
      ( forall n
        (pf : (n < sNumAgents E)%nat),
          sAgentID (sAgents E n pf) =  n) ->
  sAgents_ID_match_inv E.

Inductive sAgents_lower_border_inv : simEnv -> Prop :=
| mkAgents_lower_border_inv : 
    forall E,
      (forall n pf,
        sLocation (sAgents E n pf) == 0 ->
        sHeading (sAgents E n pf) = dRight) ->
      sAgents_lower_border_inv E.

Inductive sAgents_upper_border_inv : simEnv -> Prop :=
| mkAgents_upper_border_inv : 
    forall E,
      (forall n pf,
        sLocation (sAgents E n pf) == sPerimLength E ->
        sHeading (sAgents E n pf) = dLeft) ->
      sAgents_upper_border_inv E.

Inductive sAgents_order_dir_inv : simEnv -> Prop :=
| mkAgents_sAgents_order_inv :
    forall E,
      (forall n1 n2 pf1 pf2 (pf3 : (n1 < n2)%nat),
        (sLocation (sAgents E n1 pf1) ==
        (sLocation (sAgents E n2 pf2))) -> 
          ((sHeading (sAgents E n1 pf1) = (sHeading (sAgents E n2 pf2))) \/
          ((sHeading (sAgents E n1 pf1) = dLeft) /\
           (sHeading (sAgents E n2 pf2) = dRight)))) ->
      sAgents_order_dir_inv E.


(** An environment satisfying all of these properties is valid *)
Inductive validSimEnv : simEnv -> Prop :=
| mkValidSimEnv :
    forall E,
      sNumAgents_Pos_inv E ->
      sPerimLength_Pos_inv E ->
      sSpeed_Positive_inv E -> 
      sAgents_InPerim_inv E -> 
      sAgents_Ordered_inv E -> 
      sAgents_heading_towards_dest_inv E ->
      sAgents_dest_in_perim_inv E ->
      sAgents_ID_match_inv E ->
      sAgents_lower_border_inv E ->
      sAgents_upper_border_inv E ->
      sAgents_order_dir_inv E ->
        validSimEnv E.

(* Is there some relational name for preservation of a predicate
    under a relation? *)
Lemma simEnvEQ_Preserves_validSimEnv :
  forall E1 E2,
    simEnvEQ E1 E2 ->
    validSimEnv E1 ->
      validSimEnv E2.
Proof.
  intros. inversion H; inversion H0; do 2 constructor; subst.
  - rewrite <- H. inversion H8. auto.
  - rewrite <- H. inversion H9. auto.
  - rewrite <- H4. inversion H10. auto.
  - intros. rewrite <- H3.
    erewrite <- H2. inversion H11. auto.
  - intros. do 2 erewrite <- H2.
    inversion H12; auto.
  - intros. inversion H13.
    assert (n < sNumAgents E1)%nat by firstorder.
    assert (Qeq_opt (sDestination (sAgents E1 n H20)) (Some d)).
    { erewrite H2. rewrite H6. firstorder. } inversion H21.
    subst. symmetry in H22. apply H7 in H22.
    inversion H22; rewrite H2 in H19; erewrite <- H19;
    [eapply ltDir | eapply gtDir]; rewrite <- H2;
    subst; rewrite <- H24; eauto.
  - intros. rewrite <- H. inversion H14. eapply H7.
    rewrite H2. eauto.
  - intros. rewrite <- H2. inversion H15. eauto.
  - intros. erewrite sHeading_mor. 2: rewrite <- H2; reflexivity.
    inversion H16; subst. apply H7. rewrite <- H6.
    erewrite sLocation_mor. reflexivity. apply H2.
  - intros. erewrite sHeading_mor. 2: rewrite <- H2; reflexivity.
    inversion H17; subst. apply H7.
    rewrite H3. rewrite <- H6.
    apply sLocation_mor. apply H2.
  - intros. inversion H18; subst.
    assert (n1 < sNumAgents E1)%nat as pf1'.
    { rewrite H1; auto. }
    assert (n2 < sNumAgents E1)%nat as pf2'.
    { rewrite H1; auto. }
    assert (sLocation (sAgents E1 n1 pf1') ==
            sLocation (sAgents E1 n2 pf2')).
    { etransitivity. etransitivity.
      2: apply H6.
      apply sLocation_mor. apply H2.
      apply sLocation_mor. symmetry. apply H2.
    }
    specialize (H7 n1 n2 pf1' pf2' pf3 H19).
    inversion H7; [left | right].
    etransitivity.
    transitivity (sHeading (sAgents E1 n1 pf1')).
    apply sHeading_mor.
    symmetry; apply H2. apply H20.
    apply sHeading_mor. apply H2.
    split; destruct H20;
    [rewrite <- H20 | rewrite <- H21];
    apply sHeading_mor; symmetry; apply H2.
  Unshelve. all: rewrite H; auto.
Qed.

(** Definitions for the type of various events that require a response from agents **)
Record simLowerBorderEvent {E : simEnv} : Type :=
  mkLBEvent {
    LB_agent : simAgent;
    LB_ID : nat;
    LB_time : Q;
    
    LB_ID_pf : (LB_ID < sNumAgents E)%nat;
    LB_ID_inv : (LB_agent = sAgents E LB_ID LB_ID_pf);
    LB_path_inv : locationAfterTime
                    (sLocation LB_agent) (sHeading LB_agent)
                    (sSpeed E) LB_time 
                  == 0;
    LB_time_pos : 0 < LB_time;
  }.

Record simUpperBorderEvent {E : simEnv} : Type :=
  mkUBEvent {
    UB_agent : simAgent;
    UB_ID : nat;
    UB_time : Q;
    
    UB_ID_pf : (UB_ID < sNumAgents E)%nat;
    UB_ID_inv : (UB_agent = sAgents E UB_ID UB_ID_pf);
    UB_path_inv : locationAfterTime
                    (sLocation UB_agent) (sHeading UB_agent)
                    (sSpeed E) UB_time 
                  == sPerimLength E;
    UB_time_pos : 0 < UB_time;
  }.

Record simEndEscortEvent {E : simEnv} : Type :=
  mkEEEvent {
    EE_agent : simAgent;
    EE_ID : nat;
    EE_time : Q;
    EE_destination : Q;

    EE_ID_pf : (EE_ID < sNumAgents E)%nat;
    EE_ID_inv : (EE_agent = sAgents E EE_ID EE_ID_pf);
    EE_destination_inv : sDestination EE_agent = Some EE_destination;
    EE_heading : directionFromSourceToTarget
                  (sLocation EE_agent) (EE_destination) (sHeading EE_agent);

    EE_path_inv : locationAfterTime
                    (sLocation EE_agent) (sHeading EE_agent)
                    (sSpeed E) EE_time == EE_destination;

    EE_time_nonneg : 0 <= EE_time; 
  }.

Record simAgentEncounterEvent {E : simEnv} : Type :=
  mkAEEvent {
    AE_agent1 : simAgent;
    AE_ID1 : nat;
    AE_agent2 : simAgent;
    AE_ID2 : nat;
    AE_time : Q;
    
    AE_ID_pf1 : (AE_ID1 < sNumAgents E)%nat;
    AE_ID_inv1 : (AE_agent1 = sAgents E AE_ID1 AE_ID_pf1);
    AE_ID_pf2 : (AE_ID2 < sNumAgents E)%nat;
    AE_ID_inv2 : (AE_agent2 = sAgents E AE_ID2 AE_ID_pf2);

    AE_distance_pos : 0 < qDistance (sLocation AE_agent1) (sLocation AE_agent2);
    AE_path_inv : locationAfterTime
                    (sLocation AE_agent1) (sHeading AE_agent1)
                    (sSpeed E) AE_time
                    ==
                  locationAfterTime
                    (sLocation AE_agent2) (sHeading AE_agent2)
                    (sSpeed E) AE_time;
    AE_time_pos : 0 < AE_time;
  }.


(** Eqaulities over the various events types **)
Inductive simLowerBorderEventEQ {E : simEnv} :
  (@simLowerBorderEvent E) -> (@simLowerBorderEvent E) -> Prop :=
mkLBE_EQ :
  forall e1 e2, simAgentEQ (LB_agent e1) (LB_agent e2) ->
                LB_ID e1 = LB_ID e2 ->
                LB_time e1 == LB_time e2 ->
                  simLowerBorderEventEQ e1 e2.

Lemma simLowerBorderEventEQ_refl {E : simEnv} :
 reflexive _ (@simLowerBorderEventEQ E).
Proof. constructor; intros; firstorder. Qed.

Lemma simLowerBorderEventEQ_symm {E : simEnv} :
  symmetric _ (@simLowerBorderEventEQ E).
Proof. constructor; inversion H; firstorder. Qed.

Lemma simLowerBorderEventEQ_trans {E : simEnv} :
  transitive _ (@simLowerBorderEventEQ E).
Proof.
  constructor; inversion H; inversion H0; intros; firstorder;
  etransitivity; eauto.
Qed.

Lemma simLowerBorderEventEQ_equiv {E : simEnv} :
  Equivalence (@simLowerBorderEventEQ E).
Proof.
  constructor.
  - apply simLowerBorderEventEQ_refl.
  - apply simLowerBorderEventEQ_symm.
  - apply simLowerBorderEventEQ_trans.
Qed.

Add Parametric Relation (E : simEnv) : (@simLowerBorderEvent E) (simLowerBorderEventEQ)
  reflexivity proved by simLowerBorderEventEQ_refl
  symmetry proved by simLowerBorderEventEQ_symm
  transitivity proved by simLowerBorderEventEQ_trans
  as simLowerBorderEventEQ_rel.

Add Parametric Morphism (E : simEnv) : (@LB_agent E) with 
  signature simLowerBorderEventEQ ==> simAgentEQ as LB_agent_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@LB_ID E) with 
  signature simLowerBorderEventEQ ==> eq as LB_ID_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@LB_time E) with 
  signature simLowerBorderEventEQ ==> Qeq as LB_time_mor.
Proof. intros. inversion H. auto. Qed.

Definition locationAfterEvent_LB {E : simEnv} (e : @simLowerBorderEvent E) : Q :=
  locationAfterTime (sLocation (LB_agent e)) (sHeading (LB_agent e))
                    (sSpeed E) (LB_time e).

Add Parametric Morphism (E : simEnv) : (@locationAfterEvent_LB E) with 
  signature simLowerBorderEventEQ ==> Qeq as locationAfterEvent_LB_mor.
Proof.
  intros. unfold locationAfterEvent_LB. inversion H. subst.
  rewrite H0, H2. reflexivity.
Qed.

Inductive simUpperBorderEventEQ {E : simEnv} :
  (@simUpperBorderEvent E) -> (@simUpperBorderEvent E) -> Prop :=
mkUBE_EQ :
  forall e1 e2, simAgentEQ (UB_agent e1) (UB_agent e2) ->
                UB_ID e1 = UB_ID e2 ->
                UB_time e1 == UB_time e2 ->
                  simUpperBorderEventEQ e1 e2.

Lemma simUpperBorderEventEQ_refl {E : simEnv} :
  reflexive _ (@simUpperBorderEventEQ E).
Proof. constructor; intros; firstorder. Qed.

Lemma simUpperBorderEventEQ_symm {E : simEnv} :
  symmetric _ (@simUpperBorderEventEQ E).
Proof. constructor; inversion H; firstorder. Qed.

Lemma simUpperBorderEventEQ_trans {E : simEnv} :
  transitive _ (@simUpperBorderEventEQ E).
Proof.
  constructor; inversion H; inversion H0; intros; firstorder;
  etransitivity; eauto.
Qed.

Lemma simUpperBorderEventEQ_equiv {E : simEnv} :
  Equivalence (@simUpperBorderEventEQ E).
Proof.
  constructor.
  - apply simUpperBorderEventEQ_refl.
  - apply simUpperBorderEventEQ_symm.
  - apply simUpperBorderEventEQ_trans.
Qed.

Add Parametric Relation (E : simEnv) : (@simUpperBorderEvent E) (simUpperBorderEventEQ)
  reflexivity proved by simUpperBorderEventEQ_refl
  symmetry proved by simUpperBorderEventEQ_symm
  transitivity proved by simUpperBorderEventEQ_trans
  as simUpperBorderEventEQ_rel.

Add Parametric Morphism (E : simEnv) : (@UB_agent E) with 
  signature simUpperBorderEventEQ ==> simAgentEQ as UB_agent_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@UB_ID E) with 
  signature simUpperBorderEventEQ ==> eq as UB_ID_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@UB_time E) with 
  signature simUpperBorderEventEQ ==> Qeq as UB_time_mor.
Proof. intros. inversion H. auto. Qed.

Inductive simAgentEncounterEventEQ {E : simEnv} :
  (@simAgentEncounterEvent E) -> (@simAgentEncounterEvent E) -> Prop :=
mkAEE_EQ :
  forall e1 e2, simAgentEQ (AE_agent1 e1) (AE_agent1 e2) ->
                simAgentEQ (AE_agent2 e1) (AE_agent2 e2) -> 
                AE_ID1 e1 = AE_ID1 e2 ->
                AE_ID2 e1 = AE_ID2 e2 ->
                AE_time e1 == AE_time e2 ->
                  simAgentEncounterEventEQ e1 e2.

Lemma simAgentEncounterEventEQ_refl {E : simEnv} :
  reflexive _ (@simAgentEncounterEventEQ E).
Proof. constructor; intros; firstorder. Qed.

Lemma simAgentEncounterEventEQ_symm {E : simEnv} :
  symmetric _ (@simAgentEncounterEventEQ E).
Proof. constructor; inversion H; firstorder. Qed.

Lemma simAgentEncounterEventEQ_trans {E : simEnv} :
  transitive _ (@simAgentEncounterEventEQ E).
Proof.
  constructor; inversion H; inversion H0; intros; subst;
  etransitivity; eauto.
Qed.

Lemma simAgentEncounterEventEQ_equiv {E : simEnv} :
  Equivalence (@simAgentEncounterEventEQ E).
Proof.
  constructor.
  - apply simAgentEncounterEventEQ_refl.
  - apply simAgentEncounterEventEQ_symm.
  - apply simAgentEncounterEventEQ_trans.
Qed.

Add Parametric Relation (E : simEnv) :
    (@simAgentEncounterEvent E) (simAgentEncounterEventEQ)
  reflexivity proved by simAgentEncounterEventEQ_refl
  symmetry proved by simAgentEncounterEventEQ_symm
  transitivity proved by simAgentEncounterEventEQ_trans
  as simAgentEncounterEventEQ_rel.

Add Parametric Morphism (E : simEnv) : (@AE_agent1 E) with 
  signature simAgentEncounterEventEQ ==> simAgentEQ as AE_agent1_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@AE_agent2 E) with 
  signature simAgentEncounterEventEQ ==> simAgentEQ as AE_agent2_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@AE_ID1 E) with 
  signature simAgentEncounterEventEQ ==> eq as AE_ID1_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@AE_ID2 E) with 
  signature simAgentEncounterEventEQ ==> eq as AE_ID2_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@AE_time E) with 
  signature simAgentEncounterEventEQ ==> Qeq as AE_time_mor.
Proof. intros. inversion H. auto. Qed.


Inductive simEndEscortEventEQ {E : simEnv} :
  (@simEndEscortEvent E) -> (@simEndEscortEvent E) -> Prop :=
mkEEE_EQ :
  forall e1 e2, simAgentEQ (EE_agent e1) (EE_agent e2) ->
                EE_ID e1 = EE_ID e2 ->
                EE_time e1 == EE_time e2 ->
                EE_destination e1 == EE_destination e2 -> 
                  simEndEscortEventEQ e1 e2.

Lemma simEndEscortEventEQ_refl {E : simEnv} :
  reflexive _ (@simEndEscortEventEQ E).
Proof. constructor; intros; firstorder. Qed.

Lemma simEndEscortEventEQ_symm {E : simEnv} :
  symmetric _ (@simEndEscortEventEQ E).
Proof. constructor; inversion H; firstorder. Qed.

Lemma simEndEscortEventEQ_trans {E : simEnv} :
  transitive _ (@simEndEscortEventEQ E).
Proof.
  constructor; inversion H; inversion H0; intros; firstorder;
  etransitivity; eauto.
Qed.

Lemma simEndEscortEventEQ_equiv {E : simEnv} :
  Equivalence (@simEndEscortEventEQ E).
Proof.
  constructor.
  - apply simEndEscortEventEQ_refl.
  - apply simEndEscortEventEQ_symm.
  - apply simEndEscortEventEQ_trans.
Qed.

Add Parametric Relation (E : simEnv) :
    (@simEndEscortEvent E) (simEndEscortEventEQ)
  reflexivity proved by simEndEscortEventEQ_refl
  symmetry proved by simEndEscortEventEQ_symm
  transitivity proved by simEndEscortEventEQ_trans
  as simEndEscortEventEQ_rel.

Add Parametric Morphism (E : simEnv) : (@EE_agent E) with 
  signature simEndEscortEventEQ ==> simAgentEQ as EE_agent_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@EE_ID E) with 
  signature simEndEscortEventEQ ==> eq as EE_ID_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@EE_time E) with 
  signature simEndEscortEventEQ ==> Qeq as EE_time_mor.
Proof. intros. inversion H. auto. Qed.

Add Parametric Morphism (E : simEnv) : (@EE_destination E) with 
  signature simEndEscortEventEQ ==> Qeq as EE_destination_mor.
Proof. intros. inversion H. auto. Qed.

(* An event is simply built using one of these event types *)
Inductive simEvent {E : simEnv} : Type :=
| simEvent_LB : @simLowerBorderEvent E -> simEvent
| simEvent_UB : @simUpperBorderEvent E -> simEvent
| simEvent_AE : @simAgentEncounterEvent E -> simEvent
| simEvent_EE : @simEndEscortEvent E -> simEvent.

Definition timeOfEvent {E : simEnv} (e : @simEvent E): Q :=
  match e with
  | simEvent_LB e' => LB_time e'
  | simEvent_UB e' => UB_time e'
  | simEvent_AE e' => AE_time e'
  | simEvent_EE e' => EE_time e'
  end.

Definition locationOfEvent {E : simEnv} (e : @simEvent E): Q :=
  match e with
  | simEvent_LB e' => locationAfterTime
                        (sLocation (LB_agent e')) (sHeading (LB_agent e'))
                        (sSpeed E) (timeOfEvent e)
  | simEvent_UB e' => locationAfterTime
                        (sLocation (UB_agent e')) (sHeading (UB_agent e'))
                        (sSpeed E) (timeOfEvent e)
  | simEvent_AE e' => locationAfterTime
                        (sLocation (AE_agent1 e')) (sHeading (AE_agent1 e'))
                        (sSpeed E) (timeOfEvent e)
  | simEvent_EE e' => locationAfterTime
                        (sLocation (EE_agent e')) (sHeading (EE_agent e'))
                        (sSpeed E) (timeOfEvent e)
  end.

Definition agentIDOfEvent {E : simEnv}  (e : @simEvent E): nat :=
  match e with
  | simEvent_LB e' => LB_ID e'
  | simEvent_UB e' => UB_ID e'
  | simEvent_AE e' => AE_ID1 e'
  | simEvent_EE e' => EE_ID e'
  end.

Definition agentIDPfOfEvent {E : simEnv} (e : @simEvent E) :
(agentIDOfEvent e < sNumAgents E)%nat :=
  match e with
  | simEvent_LB e' => LB_ID_pf e'
  | simEvent_UB e' => UB_ID_pf e'
  | simEvent_AE e' => AE_ID_pf1 e'
  | simEvent_EE e' => EE_ID_pf e'
  end.

Definition agentOfEvent {E : simEnv} (e : @simEvent E) : simAgent :=
  sAgents E (agentIDOfEvent e) (agentIDPfOfEvent e).

Definition directionAfterEndEscortEvent
{E : simEnv} (e : @simEndEscortEvent E) : Direction :=
  let e' := simEvent_EE e in
    if Qeq_bool
        (locationOfEvent e')
        (agentUpperPatrolRange (agentIDOfEvent e') E (agentIDPfOfEvent e'))
    then dLeft
    else dRight.

Definition destinationAfterEncounterAgentEvent
{E : simEnv} (e : @simAgentEncounterEvent E) : option Q :=
  let e' := simEvent_AE e in
  let agent1_UB := agentUpperPatrolRange (AE_ID1 e) E (AE_ID_pf1 e) in 
  let agent1_LB := agentLowerPatrolRange (AE_ID1 e) E (AE_ID_pf1 e) in 
  let agent2_UB := agentUpperPatrolRange (AE_ID2 e) E (AE_ID_pf2 e) in 
  let agent2_LB := agentLowerPatrolRange (AE_ID2 e) E (AE_ID_pf2 e) in 
    if Qeq_bool agent1_UB agent2_LB then
      Some agent1_UB
    else if Qeq_bool agent1_LB agent2_UB then
      Some agent1_LB
    else None.

Definition directionAfterEncounterAgentEvent 
{E : simEnv} (e : @simAgentEncounterEvent E) : Direction :=
  let e' := simEvent_AE e in
  let d := destinationAfterEncounterAgentEvent e in
    match d with
    | None => sHeading (agentOfEvent e')
    | Some d' => match (locationOfEvent e') ?= (d') with
                 | Eq => sHeading (agentOfEvent e')
                 | Lt => dRight
                 | Gt => dLeft
                 end
    end.

Add Parametric Morphism E : destinationAfterEncounterAgentEvent with
  signature (@simAgentEncounterEventEQ E) ==> Qeq_opt as destinationAfterEncounterAgentEvent_mor.
Proof.
  intros. unfold destinationAfterEncounterAgentEvent.
  rewrite agentUpperPatrolRange_mor with (pf2 := AE_ID_pf1 y);
    [| reflexivity |rewrite H; reflexivity].
  rewrite agentLowerPatrolRange_mor with (pf2 := AE_ID_pf2 y);
    [| reflexivity |rewrite H; reflexivity].
  case Qeq_bool.
  - constructor. apply agentUpperPatrolRange_mor; try rewrite H; reflexivity.
  - rewrite agentLowerPatrolRange_mor with (pf2 := AE_ID_pf1 y);
    [| reflexivity |rewrite H; reflexivity].
  rewrite agentUpperPatrolRange_mor with (pf2 := AE_ID_pf2 y);
    [| reflexivity |rewrite H; reflexivity].
    case Qeq_bool; try reflexivity. constructor.
    apply agentLowerPatrolRange_mor. reflexivity.
    rewrite H. reflexivity.
Qed.

Inductive eventEQ {E : simEnv} : (@simEvent E) -> (@simEvent E) -> Prop :=
| eventEQ_LBE : forall e1 e2 e1' e2', 
    e1 = simEvent_LB e1' ->
    e2 = simEvent_LB e2' ->
    simLowerBorderEventEQ e1' e2' -> 
      eventEQ e1 e2
| eventEQ_UBE : forall e1 e2 e1' e2', 
    e1 = simEvent_UB e1' ->
    e2 = simEvent_UB e2' ->
    simUpperBorderEventEQ e1' e2' -> 
      eventEQ e1 e2
| eventEQ_AEE : forall e1 e2 e1' e2', 
    e1 = simEvent_AE e1' ->
    e2 = simEvent_AE e2' ->
    simAgentEncounterEventEQ e1' e2' -> 
      eventEQ e1 e2  
| eventEQ_EEE : forall e1 e2 e1' e2', 
    e1 = simEvent_EE e1' ->
    e2 = simEvent_EE e2' ->
    simEndEscortEventEQ e1' e2' -> 
      eventEQ e1 e2.

Lemma eventEQ_refl {E : simEnv} : reflexive _ (@eventEQ E).
Proof.
  unfold reflexive. intros. destruct x.
  - eapply eventEQ_LBE; reflexivity.
  - eapply eventEQ_UBE; reflexivity.
  - eapply eventEQ_AEE; reflexivity.
  - eapply eventEQ_EEE; try reflexivity.
Qed.

Lemma eventEQ_symm {E : simEnv} : symmetric _ (@eventEQ E).
Proof.
  unfold symmetric. intros. inversion H; subst.
  - eapply eventEQ_LBE; eauto. firstorder.
  - eapply eventEQ_UBE; eauto. firstorder.
  - eapply eventEQ_AEE; eauto. firstorder.
  - eapply eventEQ_EEE; eauto. firstorder.
Qed.

Lemma eventEQ_trans {E : simEnv} : transitive _ (@eventEQ E).
Proof.
  unfold transitive. intros. inversion H; inversion H0; subst; try congruence.
  - eapply eventEQ_LBE; eauto. etransitivity. apply H3. inversion H6. auto.
  - eapply eventEQ_UBE; eauto. etransitivity. apply H3. inversion H6. auto.
  - eapply eventEQ_AEE; eauto. etransitivity. apply H3. inversion H6. auto.
  - eapply eventEQ_EEE; eauto. etransitivity. apply H3. inversion H6. auto.
Qed.

Lemma eventEQ_equiv {E : simEnv} : Equivalence (@eventEQ E).
Proof.
  constructor.
  - apply eventEQ_refl.
  - apply eventEQ_symm.
  - apply eventEQ_trans.
Qed.

Add Parametric Relation (E : simEnv) : (@simEvent E) (@eventEQ E)
  reflexivity proved by eventEQ_refl
  symmetry proved by eventEQ_symm
  transitivity proved by eventEQ_trans
  as eventEQ_rel.

Add Parametric Morphism (E : simEnv) : (@timeOfEvent E) with 
  signature eventEQ ==> Qeq as timeOfEvent_mor.
Proof.
  intros. inversion H; subst; unfold timeOfEvent; rewrite H2; firstorder.
Qed.

Add Parametric Morphism (E : simEnv) : (@locationOfEvent E) with 
  signature eventEQ ==> Qeq as locationOfEvent_mor.
Proof.
  intros. inversion H; subst; unfold locationOfEvent.
  inversion H2; subst.
  - rewrite H0, H3. reflexivity.
  - rewrite H, H2. reflexivity.
  - rewrite H, H2. reflexivity.
  - rewrite H, H2. reflexivity.
Qed.

Add Parametric Morphism (E : simEnv) : (@agentIDOfEvent E) with 
  signature eventEQ ==> eq as agentIDOfEvent_mor.
Proof.
  intros. inversion H; subst; unfold agentIDOfEvent; try rewrite H2; firstorder.
Qed.

Add Parametric Morphism (E : simEnv) : (@agentOfEvent E) with 
  signature eventEQ ==> simAgentEQ as agentOfEvent_mor.
Proof.
  intros. inversion H; subst; unfold agentOfEvent;
  [unfold LB_agent | unfold UB_agent | unfold AE_agent1 | unfold EE_agent];
  destruct e1', e2'; simpl in *; subst; apply sAgents_mor; auto.
  all: try reflexivity.
  all: inversion H2; auto.
Qed.


Add Parametric Morphism E : directionAfterEncounterAgentEvent with
  signature (@simAgentEncounterEventEQ E) ==> eq as directionAfterEncounterAgentEvent_mor.
Proof.
  intros. unfold directionAfterEncounterAgentEvent.
  generalize (destinationAfterEncounterAgentEvent_mor E x y H). intros.
  inversion H0. inversion H; subst. unfold agentOfEvent; simpl.
  rewrite sAgents_mor; [| reflexivity |apply H5].
  reflexivity. rewrite H3. 
  assert (locationOfEvent (simEvent_AE x) == locationOfEvent (simEvent_AE y)).
  apply locationOfEvent_mor. eapply eventEQ_AEE; try reflexivity. auto.
  rewrite H4. case Qcompare.
  apply sHeading_mor. unfold agentOfEvent. simpl.
  rewrite sAgents_mor; [| reflexivity |]. reflexivity. inversion H; auto.
  all: auto.
Qed.

Add Parametric Morphism E : directionAfterEndEscortEvent with
  signature (@simEndEscortEventEQ E) ==> eq as directionAfterEndEscortEvent_mor.
Proof.
  intros. unfold directionAfterEndEscortEvent.
  assert ( locationOfEvent (simEvent_EE x) == locationOfEvent (simEvent_EE y)).
  {
    unfold locationOfEvent. apply locationAfterTime_mor; try rewrite H; try reflexivity.
    apply timeOfEvent_mor. eapply eventEQ_EEE; try reflexivity. auto.
  }
  rewrite H0. rewrite agentUpperPatrolRange_mor. 1,2 : reflexivity.
  apply agentIDOfEvent_mor. eapply eventEQ_EEE; try reflexivity. auto.
Qed. 

Inductive nextEvents (E : simEnv) : (list (@simEvent E)) -> Prop :=
|  mkNextEvents :
    forall l,
      (* all events in the list occur at the soonest possible time step *)
      (forall (e e' : (@simEvent E)), In e l -> (timeOfEvent e) <= timeOfEvent e') -> 
      (*
         all events that occur at the soonest possible time step are in
         the list -- up to equivalence with eventEQ.
      *)
      (forall e,
        (forall e' : (@simEvent E),timeOfEvent e <= timeOfEvent e') ->
        InA eventEQ e l) ->
      (* the list contains no duplicates -- up to equivalence with eventEQ*)
      NoDupA eventEQ l ->
  nextEvents E l.

(*
  For any environment, the list of nextEvents is unique
    -- up to permutation and eventEQ 
*)
Lemma nextEvents_uniq :
  forall E l l', nextEvents E l -> nextEvents E l' -> PermutationA eventEQ l l'.
Proof.
  intros.
  apply NoDupA_equivlistA_PermutationA.
  - apply eventEQ_equiv.
  - inversion H; auto.
  - inversion H0; auto.
  - constructor; intros; inversion H; subst; inversion H0; subst.
      * apply H6. intros. apply InA_alt in H1. destruct H1 as [y [H1 H1']].
        rewrite H1. apply H2. auto.
      * apply H3. intros. apply InA_alt in H1. destruct H1 as [y [H1 H1']].
        rewrite H1. apply H5. auto.
Qed.

Lemma nextEvents_time_eq :
  forall E l e1 e2,
    nextEvents E l ->
    InA eventEQ e1 l ->
    InA eventEQ e2 l ->
      timeOfEvent e1 == timeOfEvent e2.
Proof.
  intros.
  apply InA_alt in H0.
  apply InA_alt in H1.
  destruct H0 as [x [Hx H0]].
  destruct H1 as [y [Hy H1]].
  rewrite Hx, Hy.
  clear e1 e2 Hx Hy.
  inversion H; subst.
  apply (H2 _ x) in H1.
  apply (H2 _ y) in H0.
  apply Qle_antisym; auto.
Qed.

Lemma nextEvents_agent_location_inv :
  forall E l a (e1 e2 : @simEvent E),
    nextEvents E l ->
    InA eventEQ e1 l ->
    InA eventEQ e2 l ->
    agentIDOfEvent e1 = a ->
    agentIDOfEvent e2 = a -> locationOfEvent e1 == locationOfEvent e2.
Proof.
  intros.
  apply InA_alt in H0.
  apply InA_alt in H1.
  destruct H0 as [x [Hx H0]].
  destruct H1 as [y [Hy H1]].
  rewrite Hx, Hy.
  rewrite Hx in H2. rewrite Hy in H3.
  clear e1 e2  Hx Hy.
  assert (InA eventEQ x l) as H0'.
  { apply In_InA. apply eventEQ_equiv. auto. }
  assert (InA eventEQ y l) as H1'.
  { apply In_InA. apply eventEQ_equiv. auto. }
  generalize (nextEvents_time_eq E l _ _ H H0' H1'); intros.
  destruct x, y, s, s0; simpl in *; rewrite H4; subst;
  erewrite sAgents_mor; try reflexivity.
Qed.

(* Given an agent and some event affecting the agent, produces a new agent state *)
Inductive updateAgent_rel {E : simEnv} :
  simAgent -> (@simEvent E) -> simAgent -> Prop :=
| mkEvent_LB_rel :
    forall a a' e,
      simAgentEQ
        a'
        (mkRealAgent 
          dRight
          (locationOfEvent (@simEvent_LB E e))
          (sDestination a)
          (sAgentID a)) ->
  updateAgent_rel a (simEvent_LB e) a'

| mkEvent_UB_rel :
    forall a a' e,
      simAgentEQ
        a'
        (mkRealAgent
          dLeft
          (locationOfEvent (@simEvent_UB E e))
          (sDestination a) 
          (sAgentID a)) ->
  updateAgent_rel a (simEvent_UB e) a'

| mkEvent_AE_rel :
    forall a a' e,
      simAgentEQ
        a'
        (mkRealAgent
          (directionAfterEncounterAgentEvent e)
          (locationOfEvent (simEvent_AE e))
          (destinationAfterEncounterAgentEvent e) (* FIX ME:
                                                      <- This might not be correct *)
          (sAgentID a)) ->
  updateAgent_rel a (simEvent_AE e) a'

| mkEvent_EE_rel :
    forall a a' e,
      simAgentEQ
        a'
        (mkRealAgent
          (directionAfterEndEscortEvent e)
          (locationOfEvent (simEvent_EE e))
          None 
          (sAgentID a)) ->
  updateAgent_rel a (simEvent_EE e) a'.

Lemma updateAgent_rel_mor :
  forall E a1 a1' a2 a2' e e',
     simAgentEQ a1 a1' ->
     simAgentEQ a2 a2' ->
     eventEQ e e' ->
     (@updateAgent_rel E a1 e a2 -> @updateAgent_rel E a1' e' a2').
Proof.
  intros. inversion H2; subst; inversion H1; try congruence; subst;
  constructor; symmetry in H0; setoid_replace a2' with a2; auto; rewrite H3;
  constructor; simpl; auto; simpl; try apply locationAfterTime_mor; inversion H4;
  subst; try rewrite H6; try rewrite H.
  all: try reflexivity.
Qed. 

(* Ultimately, the environment processes events step by step,
    updating each relevant agent in response to a particular event.
    
    This relation is the relation that needs to hold 
    betweeen any two of these intermediate enviornments *)
Inductive updateEnvironment_intermediate_small {Env_context : simEnv} :
  simEnv -> (@simEvent Env_context) -> simEnv -> Prop :=
| mkUpdateEnvironment_intermediate_small :
    forall E e E',
      sNumAgents E = sNumAgents E' ->
      sPerimLength E == sPerimLength E' ->
      sSpeed E == sSpeed E' ->
      sTime E == sTime E' ->
      (* Everything in the environment remains unchanged except for
          the single agent involved in the event *)
      (forall n pf1 pf2, n <> agentIDOfEvent e ->
        simAgentEQ (sAgents E n pf1) (sAgents E' n pf2)) ->
      (forall n pf1 pf2, n = agentIDOfEvent e -> 
        updateAgent_rel (sAgents E n pf1) e (sAgents E' n pf2)) -> 
  updateEnvironment_intermediate_small E e E'.

Lemma updateEnvironment_intermediate_small_mor :
  forall E_cont E1 E2 E1' E2' (e e' : @simEvent E_cont),
    (simEnvEQ E1 E1') ->
    (eventEQ e e') ->
    updateEnvironment_intermediate_small E1 e E2 ->
    updateEnvironment_intermediate_small E1' e' E2' ->
      simEnvEQ E2 E2'.
Proof.
  intros.
  inversion H1; subst. inversion H2; subst.
  constructor.
  - rewrite <- H9, <- H3, H. auto.
  - intros. assert (n < sNumAgents E1)%nat by (rewrite H3; auto).
    assert (n < sNumAgents E1')%nat by (rewrite H9; auto).
    case (Nat.eq_dec n (agentIDOfEvent e')); intros.
    * assert (n = agentIDOfEvent e) by (rewrite H0; auto).
      specialize (H8 n H15 pf1 H17).
      specialize (H14 n H16 pf2 e0).
      clear H13 H7.
      inversion H0; subst;
      inversion H14; subst; inversion H8; subst;
      constructor; try rewrite H20, H19; simpl; auto.
      all: try reflexivity.
      all: try apply sAgentID_mor.
      all: try apply sDestination_mor.
      all: try apply sAgents_mor.
      all: try rewrite H18; try reflexivity; auto.
    * assert (n <> agentIDOfEvent e)%nat by (rewrite H0; auto).
      specialize (H7 n H15 pf1 H17).
      specialize (H13 n H16 pf2 n0).
      rewrite <- H13, <- H7. apply sAgents_mor; auto.
  - rewrite <- H10, <- H4, H. reflexivity.
  - rewrite <- H5, <- H11, H. reflexivity.
  - rewrite <- H6, <- H12, H. reflexivity.
Qed.


(* This is the same relation above, but transitive, wrt. a list of events *)
Inductive updateEnvironment_intermediate_big {Env_context : simEnv} :
  simEnv -> list (@simEvent Env_context) -> simEnv -> Prop :=

| mkUpdateEnvironment_intermediate_big_step :
    forall E e E',
      updateEnvironment_intermediate_small E e E' ->
  updateEnvironment_intermediate_big E (e::nil) E'

| mkUpdateEnvironment_intermediate_big_trans : 
    forall E E' e l E_int,
      updateEnvironment_intermediate_big E_int l E' ->
      updateEnvironment_intermediate_small E e E_int -> 
  updateEnvironment_intermediate_big E (e::l) E'.

Lemma updateEnvironment_intermediate_big_preserves_sNumAgents {Env_context : simEnv} :
  forall E E' (l : list (@simEvent Env_context)),
    updateEnvironment_intermediate_big E l E' ->
    sNumAgents E = sNumAgents E'.
Proof.
  intros. induction H.
  - inversion H; subst. auto.
  - rewrite <- IHupdateEnvironment_intermediate_big.
    inversion H0; subst. auto.
Qed.

Lemma updateEnvironment_intermediate_big_preserves_sPerimLength {Env_context : simEnv} :
  forall E E' (l : list (@simEvent Env_context)),
    updateEnvironment_intermediate_big E l E' ->
    sPerimLength E == sPerimLength E'.
Proof.
  intros. induction H.
  - inversion H; subst. auto.
  - rewrite <- IHupdateEnvironment_intermediate_big.
    inversion H0; subst. auto.
Qed.
  
Lemma updateEnvironment_intermediate_big_preserves_sSpeed {Env_context : simEnv} :
  forall E E' (l : list (@simEvent Env_context)),
    updateEnvironment_intermediate_big E l E' ->
    sSpeed E == sSpeed E'.
Proof.
  intros. induction H.
  - inversion H; subst. auto.
  - rewrite <- IHupdateEnvironment_intermediate_big.
    inversion H0; subst. auto.
Qed.

Lemma updateEnvironment_intermediate_big_preserves_agentIDs {Env_context : simEnv} :
  forall E E' (l : list (@simEvent Env_context)) n pf1 pf2,
    updateEnvironment_intermediate_big E l E' ->
    (sAgentID (sAgents E n pf1)) = (sAgentID (sAgents E' n pf2)).
Proof.
  intros.
  induction H.
  {
    inversion H; subst.
    case (eq_nat_dec n (agentIDOfEvent e)); intros.
    * specialize (H5 _ pf1 pf2 e0);
      inversion H5; subst; destruct e1; simpl;
      rewrite H6; simpl; reflexivity.
    * specialize (H4 _ pf1 pf2 n0).
      rewrite H4. reflexivity.
  }
  {
    assert ((n < sNumAgents E_int)%nat) as pf3.
    erewrite updateEnvironment_intermediate_big_preserves_sNumAgents; eauto.
    inversion H0; subst.
    erewrite <- IHupdateEnvironment_intermediate_big.
    case (eq_nat_dec n (agentIDOfEvent e)); intros.
    * specialize (H6 _ pf1 pf3 e0).
      inversion H6; subst; simpl; rewrite H7; simpl in *; reflexivity.
    * specialize (H5 _ pf1 pf3 n0). rewrite H5. reflexivity.
  }
Qed.

(**
    Note :
      We need these at this point, but they should be moved into
      the correct places later
**)

Lemma DirectionEQ_dec : 
  forall (d1 d2 : Direction), {d1 = d2} + {d1 <> d2}.
Proof.
  intros. destruct d1, d2.
  1, 4: left; auto.
  all: right; congruence.
Qed.

Lemma simAgentEQ_dec :
  forall a1 a2, {simAgentEQ a1 a2} + {~simAgentEQ a1 a2}.
Proof.
  destruct a1, a2.
  generalize (DirectionEQ_dec sHeading0 sHeading1); intros.
  generalize (Qeq_dec sLocation0  sLocation1); intros.
  generalize (eq_nat_dec sAgentID0  sAgentID1); intros.
  destruct sDestination1, sDestination0.
  2, 3: right; intros H_contra; inversion H_contra; simpl in *; subst.
  {
    generalize (Qeq_dec q0  q); intros.
    destruct H, H0, H1, H2.
    left. constructor; simpl; auto. constructor. auto. 
    all: right; intros H_contra; inversion H_contra; simpl in *; subst;
         try congruence.
    inversion H2. congruence.
  }
  inversion H5. inversion H5.
  {
    destruct H, H0, H1.
    left. constructor; simpl; auto. constructor. auto. 
    all: right; intros H_contra; inversion H_contra; simpl in *; subst;
         try congruence.
  }
Qed.    


(* move me to a place dealing with events *)
Lemma simLowerBorderEventEQ_dec {E : simEnv} :
  forall (e e': @simLowerBorderEvent E), 
    {simLowerBorderEventEQ e e'} + {~simLowerBorderEventEQ e e'}.
Proof.
  intros. destruct e. destruct e'.
  generalize (eq_nat_dec LB_ID0  LB_ID1); intros.
  generalize (Qeq_dec LB_time0  LB_time1); intros.  
  destruct H. destruct H0.
  left. constructor; simpl.
  rewrite LB_ID_inv1, LB_ID_inv0.
  apply sAgents_mor; try auto.
  reflexivity. auto. auto.
  all: right; intros H_contra; inversion H_contra; subst;
       simpl in *; congruence.
Qed.

Lemma simAgentEncounterEventEQ_dec {E : simEnv} :
  forall (e e': @simAgentEncounterEvent E), 
    {simAgentEncounterEventEQ e e'} + {~simAgentEncounterEventEQ e e'}.
Proof.
  intros. destruct e. destruct e'.
  generalize (eq_nat_dec AE_ID3  AE_ID5); intros.
  generalize (Qeq_dec AE_time0  AE_time1); intros.
  generalize (eq_nat_dec AE_ID4  AE_ID6); intros.
  destruct H, H0, H1.
  left. constructor; simpl.
  rewrite AE_ID_inv3, AE_ID_inv5.
  apply sAgents_mor; try auto.
  reflexivity.
  auto.
  rewrite AE_ID_inv6, AE_ID_inv4.
  apply sAgents_mor; try auto.
  reflexivity. auto. auto. auto.
  all: right; intros H_contra; inversion H_contra; subst;
       simpl in *; congruence.
Qed.


Lemma simUpperBorderEventEQ_dec {E : simEnv} :
  forall (e e': @simUpperBorderEvent E), 
    {simUpperBorderEventEQ e e'} + {~simUpperBorderEventEQ e e'}.
Proof.
  intros. destruct e. destruct e'.
  generalize (eq_nat_dec UB_ID0  UB_ID1); intros.
  generalize (Qeq_dec UB_time0  UB_time1); intros.  
  destruct H. destruct H0.
  left. constructor; simpl.
  rewrite UB_ID_inv1, UB_ID_inv0.
  apply sAgents_mor; try auto.
  reflexivity. auto. auto.
  all: right; intros H_contra; inversion H_contra; subst;
       simpl in *; congruence.
Qed.

Lemma simEndEscortEventEQ_dec {E : simEnv} :
  forall (e e': @simEndEscortEvent E), 
    {simEndEscortEventEQ e e'} + {~simEndEscortEventEQ e e'}.
Proof.
  intros. destruct e. destruct e'.
  generalize (eq_nat_dec EE_ID0  EE_ID1); intros.
  generalize (Qeq_dec EE_time0  EE_time1); intros.
  generalize (Qeq_dec EE_destination0  EE_destination1); intros.
  destruct H. destruct H0. destruct H1.
  left. constructor; simpl.
  rewrite EE_ID_inv1, EE_ID_inv0.
  apply sAgents_mor; try auto.
  reflexivity. auto. auto. auto.
  all: right; intros H_contra; inversion H_contra; subst;
       simpl in *; congruence.
Qed.


Lemma eventEQ_dec {E : simEnv} :
  forall (e e': @simEvent E), 
    {eventEQ e e'} + {~eventEQ e e'}.
Proof.
  intros. destruct e, e';
  try (right; intros H_contra; inversion H_contra; congruence).
  - destruct (simLowerBorderEventEQ_dec s s0); [left | right].
    eapply eventEQ_LBE; firstorder.
    intros H_contra. inversion H_contra; subst; congruence.
  - destruct (simUpperBorderEventEQ_dec s s0); [left | right].
    eapply eventEQ_UBE; firstorder.
    intros H_contra. inversion H_contra; subst; congruence.
  - destruct (simAgentEncounterEventEQ_dec s s0); [left | right].
    eapply eventEQ_AEE; firstorder.
    intros H_contra. inversion H_contra; subst; congruence.
  - destruct (simEndEscortEventEQ_dec s s0); [left | right].
    eapply eventEQ_EEE; firstorder.
    intros H_contra. inversion H_contra; subst; congruence.
Qed.  

Lemma InA_eventEQ_dec {E : simEnv}:
  forall (e : @simEvent E) l, {InA eventEQ e l} + {~InA eventEQ e l}.
Proof.
  intros.
  induction l.
  right. intros H_contra. inversion H_contra.
  generalize (eventEQ_dec e a); intros.
  destruct H.
  - left. left. auto.
  - destruct IHl; [ left | right].
    * right. auto.
    * intros H_contra. inversion H_contra; subst; congruence.
Qed. 

Lemma InA_eventID_dec {E : simEnv} :
  forall n (l : list (@simEvent E)),
    (exists e, agentIDOfEvent e  = n /\ InA eventEQ e l) \/
    ~ (exists e, agentIDOfEvent e = n /\ InA eventEQ e l).
Proof.
  induction l.
  + right. intros H_contra.
    destruct H_contra as [e [H0 H1]].
    inversion H1.
  + destruct IHl.
    - destruct H as [e [H0 H1]]. left.
      exists e; split; try right; auto.
    - destruct (eq_nat_dec (agentIDOfEvent a) n); [left | right].
      * exists a; split; try left; auto. reflexivity.
      * intros H_contra. destruct H_contra as [e [H0 H1]].
        inversion H1; subst. rewrite H3 in n0. congruence.
        apply H. exists e; split; auto.
Qed.

(* End note applicability *)
Lemma updateEnvironment_intermediate_big_NoOp {Env_context : simEnv} :
  forall E E' (l : list (@simEvent Env_context)) n pf1 pf2,
    updateEnvironment_intermediate_big E l E' ->
    (forall e, InA eventEQ e l -> (agentIDOfEvent e <> n)) ->
      simAgentEQ (sAgents E n pf1) (sAgents E' n pf2).
Proof.
  intros. induction H.
  + inversion H; subst. apply H5.
    intros H_contra. eapply H0. left. reflexivity. eauto.
  + etransitivity.
    2: apply IHupdateEnvironment_intermediate_big.
    inversion H1; subst.
    apply H6. 
    intros H_contra. eapply H0. left. reflexivity. eauto.
    intros. apply H0. right. auto.
  Unshelve. inversion H1. rewrite <- H2. auto.
Qed.

Lemma updateEnvironment_intermediate_big_constant_location {Env_context : simEnv}:
  forall E E' (l : list (@simEvent Env_context)) e n pf,
    updateEnvironment_intermediate_big E l E' ->
    InA eventEQ e l ->
    agentIDOfEvent e = n ->
    (forall e',   InA eventEQ e' l ->
                  (agentIDOfEvent e' = n) ->
                    locationOfEvent e == locationOfEvent e') ->
    (locationOfEvent e == sLocation (sAgents E' n pf)).
Proof.
  intros. generalize dependent e. induction H; intros.
  + inversion H; subst.
    apply InA_singleton in H0.
    assert (agentIDOfEvent e0 < sNumAgents E)%nat as pf1
      by (rewrite H3; auto).
    assert (agentIDOfEvent e0 = agentIDOfEvent e) as pf2
      by (rewrite H0; auto).
    specialize (H8 _ pf1 pf pf2);
    inversion H8; rewrite H1, H10; simpl;
    rewrite H0; reflexivity.
  + destruct (InA_eventID_dec n l).
    {
      destruct H4 as [e' [H4 H5]].
      rewrite (H3 e'); try right; try auto.
      eapply IHupdateEnvironment_intermediate_big; try auto.
      intros. rewrite <- H3; try right; try auto.
    }
    {
      assert (n < sNumAgents E_int)%nat as pf1 by
        (erewrite updateEnvironment_intermediate_big_preserves_sNumAgents; eauto).
      assert (n < sNumAgents E)%nat as pf2.
        { inversion H0; subst. rewrite H5. auto. }
      transitivity (sLocation (sAgents E_int n pf1)).
      2: { apply sLocation_mor.
           eapply updateEnvironment_intermediate_big_NoOp.
           eauto.
           intros e_contra H_contra1 H_contra2.
           apply H4. exists e_contra. split; auto.
      }
      inversion H0; subst.
      assert (eventEQ e e0) as pf3.
        {
          inversion H1; subst. symmetry. auto.
          apply False_rec. apply H4.
          exists e0. split; auto.
        }
      assert (agentIDOfEvent e0 = agentIDOfEvent e) by (rewrite pf3; auto).
      specialize (H10 (agentIDOfEvent e0) pf2 pf1 H2).
      inversion H10; subst; rewrite H11; simpl;
      rewrite <- pf3; reflexivity.
  }
Qed.
(*  
  A given environment E correctly updates all agents 
  involved in events if:

    1.) there exists a list of events satisfying the
        next events predicate for E.

    2.) there exists a trace of intermediate events
        processing the list of valid events starting at E and ending at E'.
*)

Inductive updateEnvironment_events (E : simEnv) :
  list (@simEvent E) -> simEnv -> Prop :=
| mkUpdateEnvironemnt_events :
  forall l E',
    nextEvents E l ->
    updateEnvironment_intermediate_big E l E' ->
  updateEnvironment_events E l E'.

Lemma updateEnvironment_preserves_sNumAgents :
  forall E l E',
    updateEnvironment_events E l E' ->
    sNumAgents E = sNumAgents E'.
Proof.
  intros. inversion H; subst.
  eapply updateEnvironment_intermediate_big_preserves_sNumAgents.
  eauto.
Qed.

Lemma updateEnvironment_preserves_sPerimLength :
  forall E l E',
    updateEnvironment_events E l E' ->
    sPerimLength E == sPerimLength E'.
Proof.
  intros. inversion H; subst.
  eapply updateEnvironment_intermediate_big_preserves_sPerimLength.
  eauto.
Qed.

Lemma updateEnvironment_preserves_sSpeed :
  forall E l E',
    updateEnvironment_events E l E' ->
    sSpeed E == sSpeed E'.
Proof.
  intros. inversion H; subst.
  eapply updateEnvironment_intermediate_big_preserves_sSpeed.
  eauto.
Qed.

Lemma updateEnvironment_uniq_agent_loc : 
  forall E l E' e a pf,
    updateEnvironment_events E l E' ->
    InA eventEQ e l ->
    agentIDOfEvent e = a ->
    locationOfEvent e == sLocation (sAgents E' a pf).
Proof.
  intros. induction H.
  eapply updateEnvironment_intermediate_big_constant_location;
  eauto.
  intros. 
  eapply nextEvents_agent_location_inv; eauto.
Qed.

(* Probably need these, but havent't yet 
Lemma events_enum (E : simEnv) :
  exists l, NoDupA (@eventEQ E) l /\ 
            (forall e, InA (@eventEQ E) e l).
Proof.
  admit.
Admitted.

Lemma nextEvents_ex :
  forall E,
    validSimEnv E -> exists l, nextEvents E l.
Proof.
  admit.
Admitted.

Lemma nextEvents_not_nil :
  forall E l,
    validSimEnv E -> 
    nextEvents E l ->
    l <> nil.
Proof.
 admit.
Admitted.
*)

Definition timeOfEvents_list {E : simEnv} (l : list (@simEvent E)) : Q :=
match l with
| nil => 0
| cons e l' => timeOfEvent e
end.

Lemma nextEvents_same_time :
  forall E e1 e2 l,
    nextEvents E l ->
    InA (@eventEQ E) e1 l ->
    InA (@eventEQ E) e2 l ->
      timeOfEvent e1 == timeOfEvent e2.
Proof.
  intros. inversion H; subst.
  apply InA_alt in H0.
  apply InA_alt in H1.
  destruct H0 as [x [H0 H0']].
  destruct H1 as [y [H1 H1']].
  generalize (H2 x y H0').
  generalize (H2 y x H1').
  intros.
  apply Qle_antisym; auto; rewrite H0, H1; auto.
Qed.

Inductive updateUneventfulAgent : simEnv -> simAgent -> simAgent -> Q -> Prop :=
| mkUpdateUneventfulAgent :
    forall E a a' time,
      simAgentEQ
        a'
        (mkRealAgent 
          (sHeading a)
          (locationAfterTime (sLocation a) (sHeading a) (sSpeed E) time)
          (sDestination a)
          (sAgentID a)) ->
  updateUneventfulAgent E a a' time.

Inductive updateEnvironment (E : simEnv) : 
  simEnv -> Prop :=
| mkUpdateEnvironment : 
    forall l_active E_event E_final,
      (* The following fields remain unchanged *)
      sNumAgents E = sNumAgents E_final ->
      sPerimLength E == sPerimLength E_final -> 
      sSpeed E == sSpeed E_final ->
      (** Agent state updates **)
        (* If processing all events from E yields E_event *)
      updateEnvironment_events E l_active E_event ->
        (* If every eventful agent in E_final matches the output of E_event *)
      (forall n pf1 pf2,
        (exists e, agentIDOfEvent e = n /\ InA (@eventEQ E) e l_active) ->
        simAgentEQ (sAgents E_final n pf1) (sAgents E_event n pf2)) ->
        (* If every uneventful agent has moved its speed in the time it took
           for the events to occur *)
      (forall n pf1 pf2,
        (~ exists e, agentIDOfEvent e = n /\ InA (@eventEQ E) e l_active) ->
        updateUneventfulAgent E (sAgents E n pf1)
                              (sAgents E_final n pf2)
                              (timeOfEvents_list l_active)) ->
      (** Time update **)
      (sTime E_final == sTime E + (timeOfEvents_list l_active)) ->
        updateEnvironment E E_final.



(* The name indicates where this fact is applied, but make up a better name re: the actual result *)
Lemma agentID_Event_or_Uneventful_dec {E : simEnv} : 
  forall n l, 
    (exists e : @simEvent E , agentIDOfEvent e = n /\ InA eventEQ e l) \/
    (~ exists e : @simEvent E, agentIDOfEvent e = n /\ InA eventEQ e l) .
Proof.
  intros.
  induction l.
  - right. intros H_contra.
    inversion H_contra. destruct H. inversion H0.
  - destruct IHl.
    destruct H as [e [H H0]].
    left.  exists e. split; auto.
    destruct (eq_nat_dec (agentIDOfEvent a) n).
    * left. exists a. split. auto. left. reflexivity.
    * right. intros H'.
      inversion H'. destruct H0. inversion H1; subst.
      apply n0. rewrite H3. reflexivity.
      apply H. exists x. split. reflexivity.
      auto.
Qed.

Lemma timeOfEvents_timeOfEvent_eq_nextEvents : forall E l e,
  nextEvents E l ->
  InA eventEQ e l ->
  timeOfEvent e == timeOfEvents_list l.
Proof.
  intros.
  destruct l; subst.
  inversion H0.
  eapply nextEvents_time_eq; eauto.
  left; reflexivity.
Qed.

Lemma timeOfEvents_non_neg : forall E l,
  nextEvents E l -> 
    0 <= timeOfEvents_list l.
Proof.
  destruct l.
  intros; simpl. apply Qle_refl. 
  intros. simpl.
  destruct s, s; simpl; auto;
  apply Qlt_le_weak; auto.
Qed.

Lemma updateEnvironment_time_monotone : forall E E',
  updateEnvironment E E' ->
    sTime E <= sTime E'.
Proof.
  intros.
  inversion H. rewrite H6.  
  setoid_replace (sTime E) with (sTime E + 0) at 1.
  apply Qplus_le_r.
  apply timeOfEvents_non_neg. inversion H3; auto.
  nsatz.
Qed.

Lemma updateEnvironment_distance_update :
  forall E E',
    0 <= (sSpeed E) ->  
    updateEnvironment E E' ->
    forall n pf1 pf2, 
      qDistance
        (sLocation (sAgents E n pf1))
        (sLocation (sAgents E' n pf2)) ==
      (sSpeed E) * (sTime E' - sTime E).
Proof. 
  intros E E' Hspeed.
  intros. inversion H; subst.
  rewrite H6.
  assert (n < sNumAgents E_event)%nat as pf3
    by (rewrite <- (updateEnvironment_preserves_sNumAgents _ _ _ H3); auto).
  destruct (agentID_Event_or_Uneventful_dec n l_active).
  destruct H7 as [e [eID eIn]].
  - assert (simAgentEQ (sAgents E' n pf2) (sAgents E_event n pf3)) as aEQpf
      by (apply H4; exists e; split; eauto).    
    generalize (sLocation_mor _ _ aEQpf); intros.
    erewrite qDistance_mor.
      2: reflexivity.
      2: apply H7.
    erewrite qDistance_mor.
      2: reflexivity.
      2: erewrite <- updateEnvironment_uniq_agent_loc; eauto; reflexivity.
    setoid_replace (sTime E + timeOfEvents_list l_active - sTime E) with
      (timeOfEvent e).
    2: rewrite timeOfEvents_timeOfEvent_eq_nextEvents;
          inversion H3; eauto; nsatz.
    destruct e; destruct s; subst; simpl in *;
    unfold locationAfterTime;
    [ assert (LB_ID_pf0 = pf1) by apply proof_irrelevance | 
      assert (UB_ID_pf0 = pf1) by apply proof_irrelevance |
      assert (AE_ID_pf3 = pf1) by apply proof_irrelevance |
      assert (EE_ID_pf0 = pf1) by apply proof_irrelevance ];
    subst;
    [ set (a:= (sAgents E LB_ID0 pf1)) |
      set (a:= (sAgents E UB_ID0 pf1)) |
      set (a:= (sAgents E AE_ID3 pf1)) |
      set (a:= (sAgents E EE_ID0 pf1)) ];
    destruct a; simpl;
    destruct sHeading0;
    unfold qDistance.
    1, 3, 5, 7: rewrite Qabs_pos; ring_simplify; try reflexivity;
                apply Qmult_le_0_compat; auto;
                apply Qlt_le_weak; auto.
    all: rewrite Qabs_neg; ring_simplify; try reflexivity;
         apply Qle_minus_iff; ring_simplify;
         apply Qmult_le_0_compat; auto;
         apply Qlt_le_weak; auto.
  - apply (H5 _ pf1 pf2) in H7.
    inversion H7; subst.
    transitivity (sSpeed E * timeOfEvents_list l_active).
      2: nsatz.
    rewrite qDistance_mor.
      2: reflexivity.
      2: apply sLocation_mor; apply H8.
    simpl. unfold locationAfterTime.
    set (a := (sAgents E n pf1)).
    destruct a; simpl.
    destruct sHeading0;
    unfold qDistance.
    * rewrite Qabs_pos. nsatz.
      ring_simplify. apply Qmult_le_0_compat;
      auto. apply timeOfEvents_non_neg. inversion H3. auto.
    * rewrite Qabs_neg. nsatz.
      ring_simplify.
      apply Qle_minus_iff; ring_simplify;
      apply Qmult_le_0_compat; auto.
      apply timeOfEvents_non_neg. inversion H3. auto.
Qed.

Lemma updateEnvironment_location_update :
  forall E E',
    0 <= (sSpeed E) ->  
    updateEnvironment E E' ->
    forall n pf1 pf2, 
        (sLocation (sAgents E' n pf2)) ==
        (locationAfterTime
          (sLocation (sAgents E n pf1))
          (sHeading (sAgents E n pf1))
          (sSpeed E)
          ((sTime E') - (sTime E))).
Proof.
  intros E E' Hspeed.
  intros. inversion H; subst.
  rewrite H6.
  assert (n < sNumAgents E_event)%nat as pf3
    by (rewrite <- (updateEnvironment_preserves_sNumAgents _ _ _ H3); auto).
  destruct (agentID_Event_or_Uneventful_dec n l_active).
  destruct H7 as [e [eID eIn]].
  - assert (simAgentEQ (sAgents E' n pf2) (sAgents E_event n pf3)) as aEQpf
      by (apply H4; exists e; split; eauto).    
    generalize (sLocation_mor _ _ aEQpf); intros.
    rewrite H7.
    rewrite <- updateEnvironment_uniq_agent_loc; eauto.
    assert (timeOfEvents_list l_active == timeOfEvent e).
    {
      rewrite timeOfEvents_timeOfEvent_eq_nextEvents. 
      - reflexivity.
      - inversion H3. auto.
      - auto.
    }
    rewrite H8.
    destruct e; destruct s; subst; simpl in *;
    unfold locationAfterTime;
    [ assert (LB_ID_pf0 = pf1) by apply proof_irrelevance | 
      assert (UB_ID_pf0 = pf1) by apply proof_irrelevance |
      assert (AE_ID_pf3 = pf1) by apply proof_irrelevance |
      assert (EE_ID_pf0 = pf1) by apply proof_irrelevance ];
    subst;
    [ set (a:= (sAgents E LB_ID0 pf1)) |
      set (a:= (sAgents E UB_ID0 pf1)) |
      set (a:= (sAgents E AE_ID3 pf1)) |
      set (a:= (sAgents E EE_ID0 pf1)) ];
    destruct a; simpl;
    destruct sHeading0;
    unfold qDistance; nsatz.
  - apply (H5 _ pf1 pf2) in H7.
    inversion H7; subst.
    rewrite H8; simpl.
    apply locationAfterTime_mor; try reflexivity.
    nsatz.
Qed.

Lemma updateEnvironment_location_decreased :
  forall E E' n pf1 pf2,
    0 <= (sSpeed E) ->
    updateEnvironment E E' ->
    sLocation (sAgents E' n pf2) < sLocation (sAgents E n pf1) ->
      (sHeading (sAgents E n pf1)) = dLeft.
Proof.
  intros.
  case_eq (sHeading (sAgents E n pf1)); intros; auto.
  rewrite (updateEnvironment_location_update E E' H H0 n pf1 pf2) in H1.
  unfold locationAfterTime in H1.
  rewrite H2 in H1.
  apply Qlt_not_le in H1.
  apply False_rec. apply H1.
  setoid_replace (sLocation (sAgents E n pf1))
    with (sLocation (sAgents E n pf1) + 0) at 1. 
  apply Qplus_le_r.
  apply Qmult_le_0_compat; try auto.
  generalize (updateEnvironment_time_monotone _ _ H0); intros.
  apply Qle_minus_iff in H3.
  setoid_replace (sTime E' - sTime E) with (sTime E' + - sTime E); try nsatz.
  auto. nsatz.
Qed.

Lemma updateEnvironment_location_increased :
  forall E E' n pf1 pf2,
    0 <= (sSpeed E) ->
    updateEnvironment E E' ->
    sLocation (sAgents E n pf1) < sLocation (sAgents E' n pf2) ->
      (sHeading (sAgents E n pf1)) = dRight.
Proof.
  intros.
  case_eq (sHeading (sAgents E n pf1)); intros; auto.
  rewrite (updateEnvironment_location_update E E' H H0 n pf1 pf2) in H1.
  unfold locationAfterTime in H1.
  rewrite H2 in H1.
  apply Qlt_not_le in H1.
  apply False_rec. apply H1.
  setoid_replace (sLocation (sAgents E n pf1))
    with (sLocation (sAgents E n pf1) + 0) at 2. 
  apply Qplus_le_r.
  apply Qle_minus_iff. rewrite Qopp_involutive.
  setoid_replace (zero + sSpeed E * (sTime E' - sTime E)) with
    (sSpeed E * (sTime E' - sTime E)).
  apply Qmult_le_0_compat; try auto.
  generalize (updateEnvironment_time_monotone _ _ H0); intros.
  apply Qle_minus_iff in H3; auto.
  all: nsatz.
Qed.

Lemma updateEnvironment_location_0_time:
  forall E E' n pf1 pf2,
    0 <= (sSpeed E) ->
    updateEnvironment E E' ->
    (sTime E == sTime E') -> 
    sLocation (sAgents E n pf1) == sLocation (sAgents E' n pf2).
Proof.
  intros.  
  rewrite (updateEnvironment_location_update _ _ H H0 _ pf1 pf2), H1.
  unfold locationAfterTime. destruct sHeading; nsatz.
Qed.

Lemma timeOfEvents_not_0_not_nil :
  forall E l,
    @timeOfEvents_list E l <> 0 -> 
    l <> nil.
Proof.
  intros. induction l. simpl in *. apply False_rec. apply H. auto.
  congruence.
Qed.

Lemma updateEnvironment_preserves_sNumAgents_Pos :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sNumAgents_Pos_inv E'.
Proof.
  intros. constructor.
  inversion H. inversion H1. subst.
  inversion H0; subst.
  rewrite <- H12; auto.
Qed. 

Lemma updateEnvironment_preserves_sPerimLength_Pos :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sPerimLength_Pos_inv E'.
Proof.
  intros. constructor.
  inversion H. inversion H2. subst.
  inversion H0; subst. rewrite <- H14. auto.
Qed.

Lemma updateEnvironment_preserves_sSpeed_Pos :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sSpeed_Positive_inv E'.
Proof.
  intros. constructor.
  inversion H. inversion H3. subst.
  inversion H0; subst. rewrite <- H15. auto.
Qed.

Lemma updateEnvironment_preserves_sAgents_InPerim :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_InPerim_inv E'.
Proof.
  intros. constructor;
  inversion H0; inversion H; subst; auto; intros.
  generalize (updateEnvironment_time_monotone _ _ H0); intros time_case.
  inversion H11; subst.
  assert (n < sNumAgents E)%nat as pf1 by (rewrite H1; auto).
  case (Qle_lt_or_eq _ _ time_case); intros.
  2: {
    setoid_replace (sLocation (sAgents E' n pf)) with
            (sLocation (sAgents E n pf1)).
    inversion H12; subst. rewrite <- H2. apply H21.
    rewrite (updateEnvironment_location_update
                _ _ (Qlt_le_weak _ _ H8) H0 _ pf1 pf).
    rewrite H20. unfold locationAfterTime.
    inversion H12. destruct (H21 n pf1).
    destruct (sHeading);
    setoid_replace (sSpeed E * (sTime E' - sTime E')) with 0;
    try nsatz; eapply Qle_trans; try apply H22;
    apply Qle_lteq; right; nsatz.
  }
  {
    case (Qlt_le_dec (sLocation (sAgents E' n pf)) 0); intros.
    intros.
    {
      apply False_rec.
      assert (sHeading (sAgents E n pf1) = dLeft).
      { eapply updateEnvironment_location_decreased; eauto.
        2: eapply Qlt_le_trans; eauto.
        - apply Qlt_le_weak; auto.
        - inversion H12; subst. specialize (H21 n pf1).
          inversion H21; auto.
      }
      assert (~ sLocation (sAgents E n pf1) ==0).
      { intros H_contra.
        inversion H17; subst. rewrite H22 in H21.
        congruence. auto.
      }
      set (eventTime := ((sLocation (sAgents E n pf1)) / sSpeed E)).
      assert (locationAfterTime
                (sLocation (sAgents E n pf1))
                (sHeading (sAgents E n pf1))
                (sSpeed E) eventTime
              == 0) as locationPf.
      { unfold eventTime. rewrite H21. simpl.
        setoid_replace
          (sSpeed E * (sLocation (sAgents E n pf1) / sSpeed E)) with
          (sLocation (sAgents E n pf1)).
        nsatz.  rewrite Qmult_div_r. reflexivity.
        apply Qlt_not_eq in H8. congruence.
      }
      assert (0 < eventTime) as timePf.
      { unfold eventTime. 
        apply Qlt_shift_div_l; auto. ring_simplify.
        apply QOrder.le_neq_lt. inversion H12.
        apply H23. intros H_contra. apply H22.
        symmetry. auto. 
      }
      remember (simEvent_LB (mkLBEvent E
                 (sAgents E n pf1)
                  n
                  eventTime
                  pf1
                  eq_refl
                  locationPf
                  timePf)) as eventContra.
      assert (eventTime < timeOfEvents_list l_active).
      {
        erewrite (updateEnvironment_location_update E E')
          with (pf1 := pf1) in q.
        rewrite <- locationPf in q.
        unfold locationAfterTime in q.
        rewrite H21 in q.
        setoid_replace (sTime E' - sTime E)
          with (timeOfEvents_list l_active) in q.
        setoid_replace
          (sLocation (sAgents E n pf1) -
            sSpeed E * timeOfEvents_list l_active)
        with
          (sLocation (sAgents E n pf1) +
            - (sSpeed E * timeOfEvents_list l_active)) in q; try nsatz.
        setoid_replace (sLocation (sAgents E n pf1) - sSpeed E * eventTime)
          with (sLocation (sAgents E n pf1) + - (sSpeed E * eventTime)) in q; try nsatz.
        rewrite Qplus_lt_r in q.
        apply Qmult_lt_l with (z:= sSpeed E); auto.
        apply Qlt_minus_iff. apply Qlt_minus_iff in q.
        eapply QOrder.lt_eq. exact q. nsatz.
        rewrite H7. nsatz.
        apply Qlt_le_weak. auto.
        auto.
      }
      assert (InA eventEQ eventContra l_active) as contraIn.
      { inversion H4; subst. inversion H24; subst.
        apply H27.
        assert (l_active <> nil).
        { apply timeOfEvents_not_0_not_nil.
          intros H_contra. rewrite H_contra in H7.
          rewrite H7 in H20.
          setoid_replace  (_+_ (sTime E) 0) with (sTime E) in H20.
          apply Qlt_not_eq in H20. apply H20. reflexivity. nsatz.
        }
        destruct l_active. congruence. clear H28.
        intros; simpl.
        apply Qle_trans with (y := (timeOfEvent s)).
        rewrite timeOfEvents_timeOfEvent_eq_nextEvents.
        apply Qlt_le_weak. eauto. eauto. left. auto.
        reflexivity. apply H26. left. auto.
      }
      apply (Qlt_not_eq _ _ H23).
      erewrite <- timeOfEvents_timeOfEvent_eq_nextEvents.
      3: exact contraIn.
      rewrite HeqeventContra; simpl.
      reflexivity. inversion H4; auto.
    }
    case (Qlt_le_dec (sPerimLength E') (sLocation (sAgents E' n pf))); intros.
    {
      apply False_rec.
      assert (sHeading (sAgents E n pf1) = dRight).
      { eapply updateEnvironment_location_increased with (pf2 := pf).
        - apply Qlt_le_weak; auto.
        - eauto.
        - eapply Qle_lt_trans; eauto.
          inversion H12; subst. specialize (H21 n pf1).
          inversion H21. rewrite <- H2. auto.
      }
      assert (~ sLocation (sAgents E n pf1) == (sPerimLength E)).
      { intros H_contra.
        inversion H18; subst. rewrite H22 in H21.
        congruence. auto.
      }
      set (eventTime :=
        ((sPerimLength E) -(sLocation (sAgents E n pf1))) / sSpeed E).
      assert (locationAfterTime
                ((sLocation (sAgents E n pf1)))
                (sHeading (sAgents E n pf1))
                (sSpeed E) eventTime
              == (sPerimLength E)) as locationPf.
      { unfold eventTime. rewrite H21. simpl.
        setoid_replace
          (sSpeed E * ((sPerimLength E - sLocation (sAgents E n pf1))
            / sSpeed E)) with
          (sPerimLength E - sLocation (sAgents E n pf1)).
        nsatz.  rewrite Qmult_div_r. reflexivity.
        apply Qlt_not_eq in H8. congruence.
      }
      assert (0 < eventTime) as timePf.
      { unfold eventTime. 
        apply Qlt_shift_div_l; auto.
        setoid_replace (0 * sSpeed E) with 0 by nsatz.
        apply QOrder.le_neq_lt. inversion H12; subst.
        setoid_replace (sPerimLength E - sLocation (sAgents E n pf1))
          with (sPerimLength E + - sLocation (sAgents E n pf1)).
        rewrite <- Qle_minus_iff.
        apply H23. nsatz.
        setoid_replace (sPerimLength E - sLocation (sAgents E n pf1))
          with (sPerimLength E + - sLocation (sAgents E n pf1)); try nsatz.
        intros Hcontra.
        assert (sPerimLength E == sLocation (sAgents E n pf1)). nsatz.
        inversion H18; subst. symmetry in H23. apply H24 in H23.
        congruence.
      }
      remember (simEvent_UB (mkUBEvent E
                 (sAgents E n pf1)
                  n
                  eventTime
                  pf1
                  eq_refl
                  locationPf
                  timePf)) as eventContra.
      assert (eventTime < timeOfEvents_list l_active).
      {
        rewrite <- H2, <- locationPf in q0.
        erewrite (updateEnvironment_location_update E E')
          with (pf1 := pf1) in q0.
        unfold locationAfterTime in q0.
        rewrite H21 in q0.
        setoid_replace (sTime E' - sTime E)
          with (timeOfEvents_list l_active) in q0.
        rewrite Qplus_lt_r in q0.
        apply Qmult_lt_l with (z:= sSpeed E); auto.
        rewrite H7. nsatz. apply Qlt_le_weak. auto.
        auto.
      }
      assert (InA eventEQ eventContra l_active) as contraIn.
      { inversion H4; subst. inversion H24; subst.
        apply H27.
        assert (l_active <> nil).
        { apply timeOfEvents_not_0_not_nil.
          intros H_contra. rewrite H_contra in H7.
          rewrite H7 in H20.
          setoid_replace  (_+_ (sTime E) 0) with (sTime E) in H20.
          apply Qlt_not_eq in H20. apply H20. reflexivity. nsatz.
        }
        destruct l_active. congruence. clear H28.
        intros; simpl.
        apply Qle_trans with (y := (timeOfEvent s)).
        rewrite timeOfEvents_timeOfEvent_eq_nextEvents.
        apply Qlt_le_weak. eauto. eauto. left. auto.
        reflexivity. apply H26. left. auto.
      }
      apply (Qlt_not_eq _ _ H23).
      erewrite <- timeOfEvents_timeOfEvent_eq_nextEvents.
      3: exact contraIn.
      rewrite HeqeventContra; simpl.
      reflexivity. inversion H4; auto.
    }
    split; auto.
  }
Qed.

Lemma updateEnvironment_preserves_sAgents_Ordered :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_Ordered_inv E'.
Proof.
  intros. constructor.
  intros.
  destruct (Qlt_le_dec (sLocation (sAgents E' n2 pf2))
                       (sLocation (sAgents E' n1 pf1))); auto.
  apply False_rec.
  assert (n1 < sNumAgents E)%nat as pf1'.
  { inversion H0; subst. rewrite H1. auto. }
  assert (n2 < sNumAgents E)%nat as pf2'.
  { inversion H0; subst. rewrite H1. auto.  }
  assert (0 <= sSpeed E) as speedPf.
  { apply Qlt_le_weak. inversion H; subst. inversion H3; auto. }
  generalize (updateEnvironment_location_update
                E E' speedPf H0 n1 pf1' pf1); intros.
  generalize (updateEnvironment_location_update
                E E' speedPf H0 n2 pf2' pf2); intros.
  rewrite H1, H2 in q.
  inversion H0; subst.
  generalize (updateEnvironment_time_monotone _ _ H0); intros time_case.
  destruct (Qle_lt_or_eq _ _ time_case).
  2: { generalize H1, H2, q.
       setoid_rewrite H10.
       setoid_replace (sTime E' - sTime E') with 0.
       2: nsatz.
       setoid_replace
        (locationAfterTime (sLocation (sAgents E n1 pf1'))
          (sHeading (sAgents E n1 pf1')) (sSpeed E) zero)
        with (sLocation (sAgents E n1 pf1')).
       setoid_replace
        (locationAfterTime (sLocation (sAgents E n2 pf2'))
          (sHeading (sAgents E n2 pf2')) (sSpeed E) zero)
        with (sLocation (sAgents E n2 pf2')).
       intros.
       inversion H; subst.
       inversion H18; subst.
       apply (Qle_not_lt _ _ (H25 n1 n2 pf1' pf2' pf3) H13).
       unfold locationAfterTime. destruct sHeading; nsatz.
       unfold locationAfterTime.
       destruct (sHeading (sAgents E n1 pf1')); nsatz.
  }
  clear time_case.
  assert (sLocation (sAgents E n1 pf1') <= (sLocation (sAgents E n2 pf2'))).
  {
    inversion H; subst. inversion H15; subst. apply H22. auto.
  }
  destruct (Qle_lt_or_eq _ _ H11); clear H11.
  2: {
        rewrite H12 in q.
        generalize q.
        unfold locationAfterTime.
        inversion H; subst. inversion H22; subst.
        specialize (H23 n1 n2 pf1' pf2' pf3 H12).
        destruct H23.
        {
          rewrite H23. destruct sHeading;
          intros; apply (Qlt_not_eq _ _ q0); reflexivity.
        }
    inversion H23. rewrite H24, H25.
    rewrite Qlt_minus_iff.
    setoid_replace
      (sLocation (sAgents E n2 pf2') - sSpeed E * (sTime E' - sTime E) +
        - (sLocation (sAgents E n2 pf2') + sSpeed E * (sTime E' - sTime E)))
    with ( -( (1+1) * sSpeed E * (sTime E' - sTime E))).
    2: nsatz.
    apply Qle_not_lt.
    rewrite Qle_minus_iff, Qopp_involutive.
    ring_simplify.
    apply Qmult_le_0_compat.
    apply Qmult_le_0_compat.
    setoid_replace 0 with (0 + 0) at 1.
    apply Qplus_le_compat; unfold Qle; simpl; 
    apply Z.le_0_1.
    nsatz.
    apply Qlt_le_weak. inversion H; subst.
    inversion H14. auto.
    apply Qlt_minus_iff in H10.
    apply Qlt_le_weak. apply H10.
  }
  {
    case_eq (sHeading (sAgents E n1 pf1'));
    case_eq (sHeading (sAgents E n2 pf2'));
    intros.
    - generalize q; apply Qle_not_lt;
      unfold locationAfterTime; rewrite H11, H13.
      rewrite Qle_minus_iff; ring_simplify; apply Qlt_le_weak;
      rewrite Qlt_minus_iff in H12; apply H12.
    - generalize q; apply Qle_not_lt;
      unfold locationAfterTime; rewrite H11, H13.
      apply Qplus_le_compat; apply Qlt_le_weak.
      auto.
      assert (0 * (sTime E' - sTime E) < sSpeed E * (sTime E' - sTime E)).
      { apply Qmult_lt_compat_r. rewrite Qlt_minus_iff in H10.
        apply H10. inversion H; subst. inversion H16; auto.
      }
      eapply Qlt_trans. 
      2: eauto. apply Qlt_minus_iff.
      setoid_replace 0 with (0 * (sTime E' - sTime E)) at 1. 2: nsatz.
      rewrite Qopp_involutive.
      setoid_replace
        (0 * (sTime E' - sTime E) + sSpeed E * (sTime E' - sTime E))
      with (sSpeed E * (sTime E' - sTime E)).
      apply H14. nsatz.
    - set ((((sLocation (sAgents E n2 pf2')) -
          (sLocation (sAgents E n1 pf1'))) / (1 +1))/ (sSpeed E))
        as eventTime.
      assert (0 < qDistance (sLocation (sAgents E n1 pf1'))
                            (sLocation (sAgents E n2 pf2'))) as distPf.
      {
        unfold qDistance. rewrite Qabs_neg.
        setoid_replace
          (- (sLocation (sAgents E n1 pf1') - sLocation (sAgents E n2 pf2')))
          with (sLocation (sAgents E n2 pf2') + - (sLocation (sAgents E n1 pf1'))).
        2: nsatz. 
        rewrite <- Qlt_minus_iff. auto.
        apply Qle_minus_iff.
        setoid_replace
          (0 + - (sLocation (sAgents E n1 pf1') - sLocation (sAgents E n2 pf2')))
          with (sLocation (sAgents E n2 pf2') + - (sLocation (sAgents E n1 pf1'))).
        2: nsatz.
        rewrite <- Qle_minus_iff. apply Qlt_le_weak. auto.
      }
      assert (0 < eventTime) as timePf.
      {
        unfold eventTime.
        apply Qlt_shift_div_l.
        inversion H; subst. inversion H16; subst; auto.
        setoid_replace (0 * sSpeed E) with 0.
        apply Qlt_shift_div_l. reflexivity.
        setoid_replace (0 * (1 + 1)) with 0.
        rewrite Qlt_minus_iff in H12; auto.
        all: nsatz.
      }
      assert (locationAfterTime (sLocation (sAgents E n1 pf1'))
                (sHeading (sAgents E n1 pf1')) (sSpeed E) eventTime
               ==
              locationAfterTime (sLocation (sAgents E n2 pf2'))
                (sHeading (sAgents E n2 pf2')) (sSpeed E) eventTime)
        as spacePf.
      {
        unfold locationAfterTime. rewrite H11, H13.
        setoid_replace (sSpeed E * eventTime) with
                ((sLocation (sAgents E n2 pf2') -
                  sLocation (sAgents E n1 pf1')) /(1+1)).
        2:{
          unfold eventTime.
          rewrite Qmult_div_r. nsatz.
          SearchAbout Qlt Qeq not.
          inversion H; subst. inversion H16; subst.
          apply Qlt_not_eq in H25. congruence.
        } SearchAbout Qeq Qplus.
        rewrite <- Qplus_inj_r with
          (z := (sLocation (sAgents E n2 pf2') -
                 sLocation (sAgents E n1 pf1')) / (1 + 1)).
        field_simplify. reflexivity.
      }
      set (simEvent_AE (mkAEEvent E
              (sAgents E n1 pf1')
              n1
              (sAgents E n2 pf2')
              n2
              eventTime
              pf1' eq_refl
              pf2' eq_refl
              distPf
              spacePf timePf)) as eventContra.
      assert (eventTime < (timeOfEvents_list l_active)).
      {
        assert (l_active <> nil).
        { eapply timeOfEvents_not_0_not_nil.
          intros H_contra.
          assert (0 < timeOfEvents_list l_active).
          setoid_replace (timeOfEvents_list l_active)
            with (sTime E'  +- sTime E).
          rewrite <- Qlt_minus_iff. auto.
          rewrite H9. nsatz.
          apply Qlt_not_eq in H14.
          rewrite H_contra in H14.
          apply H14. reflexivity.
        }
        destruct (Qlt_le_dec eventTime
                             (timeOfEvents_list l_active)); auto.
        apply False_rec.
        assert (locationAfterTime (sLocation (sAgents E n1 pf1'))
                  (sHeading (sAgents E n1 pf1')) (sSpeed E)
                  (timeOfEvents_list l_active) <=
                locationAfterTime (sLocation (sAgents E n1 pf1'))
                  (sHeading (sAgents E n1 pf1')) (sSpeed E) eventTime).
        unfold locationAfterTime. rewrite H13.
        apply Qplus_le_r.
        rewrite  Rmul_comm.
        rewrite  Rmul_comm with (y := eventTime) (x:= sSpeed E).
        apply Qmult_le_compat_r. auto.
        apply Qlt_le_weak. inversion H; subst. inversion H17. auto.
        all: try (exact Qsrt).
        assert (locationAfterTime (sLocation (sAgents E n2 pf2'))
                  (sHeading (sAgents E n2 pf2')) (sSpeed E) eventTime <=
                locationAfterTime (sLocation (sAgents E n2 pf2'))
                  (sHeading (sAgents E n2 pf2')) (sSpeed E)
                  (timeOfEvents_list l_active)).
        unfold locationAfterTime. rewrite H11.
        apply Qplus_le_r.
        apply Qopp_le_compat.
        rewrite  Rmul_comm.
        rewrite  Rmul_comm with (y := eventTime) (x:= sSpeed E).
        apply Qmult_le_compat_r. auto.
        apply Qlt_le_weak. inversion H; subst. inversion H18. auto.
        all: try (exact Qsrt).
        rewrite spacePf in H15.
        assert (locationAfterTime (sLocation (sAgents E n1 pf1'))
                  (sHeading (sAgents E n1 pf1')) (sSpeed E)
                  (timeOfEvents_list l_active) <= 
                locationAfterTime (sLocation (sAgents E n2 pf2'))
                  (sHeading (sAgents E n2 pf2')) (sSpeed E)
                  (timeOfEvents_list l_active)).
        eapply Qle_trans. apply H15.
        apply H16.  
        apply (Qlt_not_le) in q. apply q.
        eapply Q.Proper_instance_0.
        3: exact H17.
        all: apply locationAfterTime_mor; try reflexivity.
        all: rewrite H9; nsatz.
      }
      assert (InA eventEQ eventContra l_active).
      { assert (l_active <> nil).
        { eapply timeOfEvents_not_0_not_nil.
          intros H_contra.
          assert (0 < timeOfEvents_list l_active).
          setoid_replace (timeOfEvents_list l_active)
            with (sTime E'  +- sTime E).
          rewrite <- Qlt_minus_iff. auto.
          rewrite H9. nsatz. rewrite H_contra in H15.
          apply Qlt_irrefl in H15. auto.
        }
      destruct l_active. congruence.
      inversion H6; subst. inversion H16; subst.
      apply H19. intros.
      eapply Qle_trans.
      unfold eventContra; simpl. 
      apply Qlt_le_weak. apply H14.
      apply H18. left. reflexivity.
    }
      apply (Qlt_not_eq _ _ H14).
      rewrite  <- timeOfEvents_timeOfEvent_eq_nextEvents; eauto.
      unfold eventContra. reflexivity. inversion H6; auto.
    - generalize q; apply Qle_not_lt;
      unfold locationAfterTime; rewrite H11, H13.
      rewrite Qle_minus_iff; ring_simplify; apply Qlt_le_weak;
      rewrite Qlt_minus_iff in H12; apply H12.
  }
Qed.

Lemma updateEnvironment_preserves_sAgents_headingtowards_dest :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_heading_towards_dest_inv E'.
Proof.
Admitted.

Lemma updateEnvironment_preserves_sAgents_dest_in_perim :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_dest_in_perim_inv E'.
Proof.
Admitted.

Lemma updateEnvironment_preserves_sAgents_ID_match:
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_ID_match_inv E'.
Proof.
  intros. inversion H0; subst.
  constructor. intros.
  assert (n < sNumAgents E)%nat as pf1
      by (rewrite H1; auto). 
  assert (n < sNumAgents E_event)%nat as pf2 by
    (erewrite <- updateEnvironment_preserves_sNumAgents; eauto).
  destruct (agentID_Event_or_Uneventful_dec n l_active).
  - specialize (H5 n pf pf2 H8).
    rewrite H5. inversion H4; subst.
    erewrite <- updateEnvironment_intermediate_big_preserves_agentIDs; eauto.
    inversion H; subst. inversion H18; auto.
  - specialize (H6 n pf1 pf H8).
    inversion H6; subst. rewrite H9.
    simpl. inversion H; subst. inversion H17. auto.
  Unshelve. auto.
Qed.

Lemma updateEnvironment_preserves_sAgents_lower_border :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_lower_border_inv E'.
Proof.
Admitted.

Lemma updateEnvironment_preserves_sAgents_upper_border :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_upper_border_inv E'.
Proof.
Admitted.

Lemma updateEnvironment_preserves_sAgents_order_dir :
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      sAgents_order_dir_inv E'.
Proof.
Admitted.

Lemma updateEnvironment_valid : 
  forall E E',
    validSimEnv E ->
    updateEnvironment E E' ->
      validSimEnv E'.
Proof.
  intros. constructor.
  eapply updateEnvironment_preserves_sNumAgents_Pos; eauto. (* done *)
  eapply updateEnvironment_preserves_sPerimLength_Pos; eauto. (* doned *)
  eapply updateEnvironment_preserves_sSpeed_Pos; eauto. (* done *)
  eapply updateEnvironment_preserves_sAgents_InPerim; eauto. (* done *)
  eapply updateEnvironment_preserves_sAgents_Ordered; eauto. (* done *)
  eapply updateEnvironment_preserves_sAgents_headingtowards_dest; eauto.
  eapply updateEnvironment_preserves_sAgents_dest_in_perim; eauto.
  eapply updateEnvironment_preserves_sAgents_ID_match; eauto. (* done *)
  eapply updateEnvironment_preserves_sAgents_lower_border; eauto.
  eapply updateEnvironment_preserves_sAgents_upper_border; eauto.
  eapply updateEnvironment_preserves_sAgents_order_dir; eauto.
Qed.  


(* Begin EOF scratch 
  intros. constructor;
  inversion H0; inversion H; subst; constructor; auto.
  + rewrite <- H1. inversion H9; auto.
  + rewrite <- H2. inversion H10; auto.
  + rewrite <- H3. inversion H11; auto.
  + intros. 
    inversion H11.
    apply Qlt_le_weak in H8.
    assert (n < sNumAgents E)%nat as pf1
      by (rewrite H1; auto).
    specialize (updateEnvironment_location_update E E' H8 H0 n pf1 pf); intros.
    rewrite H20.
    split.
    {
      case (Qlt_le_dec
                (locationAfterTime
                  (sLocation (sAgents E n pf1))
                  (sHeading (sAgents E n pf1)) 
                  (sSpeed E) (sTime E' - sTime E))
                0); intros; try auto. subst.
      assert (0 <= (sTime E' - sTime E)).
      {
        generalize (updateEnvironment_time_monotone _ _ H0); intros.
        apply Qle_minus_iff in H19. auto.
      }
      assert (sHeading (sAgents E n pf1)= dLeft).
      {
        apply updateEnvironment_location_decreased with (pf2 := pf); try eauto.
        apply Qlt_le_trans with (y:=0).
        rewrite H20; auto. inversion H12.
        apply H21.
      }
      assert(
              locationAfterTime
                (sLocation (sAgents E n pf1))
                (sHeading (sAgents E n pf1)) 
                (sSpeed E)
                (sLocation (sAgents E n pf1) / sSpeed E) 
              == 0).
      {
        unfold locationAfterTime. rewrite H21.
        field_simplify. nsatz.
        inversion H11; subst.
        apply Qlt_not_eq in H22. congruence.
      }
      assert (sLocation (sAgents E n pf1) / sSpeed E < timeOfEvents_list l_active).
      {
        admit.
      }
      assert (0 < (sLocation (sAgents E n pf1) / sSpeed E)).
      {
        admit.
      }
      remember (simEvent_LB (mkLBEvent E
                  (sAgents E n pf1)
                  n
                  (sLocation (sAgents E n pf1) / sSpeed E)
                  pf1
                  eq_refl
                  H22
                  H24)) as e_contra.
      assert (InA eventEQ e_contra l_active).
      inversion H4; subst.
      inversion H25; subst.
      apply H28.
      intros. simpl.
      assert (l_active <> nil).
      apply timeOfEvents_not_0_not_nil.
      intros time_contra.
      assert (sLocation (sAgents E n pf1) == (sLocation (sAgents E' n pf))). 
      apply updateEnvironment_location_0_time; auto. rewrite H7.
      rewrite time_contra. nsatz.
      rewrite <- H20 in q.
      inversion H15; subst.
      apply Qlt_not_eq in q. 
      SearchAbout Qle Qlt.
      apply 
      subst. nsatz.
    }
    {
      case (Qlt_le_dec
                (sPerimLength E')
                (locationAfterTime
                  (sLocation (sAgents E n pf1))
                  (sHeading (sAgents E n pf1)) 
                  (sSpeed E) (sTime E' - sTime E))); intros; try auto.
    }
  {

    SearchAbout Qle sumbool.
    erewrite updateEnvironment_distance_update.
 rewrite <- H2. inversion H12; auto.
    subst.
    assert (n < sNumAgents E)%nat as pf1
      by (rewrite H1; auto).
    assert (qDistance
            (sLocation (sAgents E n pf1))
            (sLocation (sAgents E' n pf)) ==
          (sSpeed E) * (sTime E' - sTime E)).
    {
      apply updateEnvironment_distance_update; auto.
      apply Qlt_le_weak. inversion H11. auto.
    }
    destruct (qDistance_or (sLocation (sAgents E' n pf))
                           (sLocation (sAgents E n pf1)));
    rewrite qDistance_symm in H18;
    rewrite H17 in H18;
    rewrite H18;
    split.
    admit. admit. admit. admit.
  + intros. admit.
  + intros. admit.
  + intros. admit.
  + intros. subst.
    assert (n < sNumAgents E)%nat as pf1
      by (rewrite H1; auto). 
    assert (n < sNumAgents E_event)%nat as pf2 by
      (erewrite <- updateEnvironment_preserves_sNumAgents; eauto).
    destruct (agentID_Event_or_Uneventful_dec n l_active).
    - specialize (H5 n pf pf2 H8).
      rewrite H5. inversion H4; subst.
      erewrite <- updateEnvironment_intermediate_big_preserves_agentIDs; eauto.
      inversion H; subst. inversion H26; auto.
    - specialize (H6 n pf1 pf H8).
      inversion H6; subst. rewrite H17.
      simpl. inversion H; subst. inversion H25. auto.
Unshelve.
  rewrite (updateEnvironment_preserves_sNumAgents E l_active E_event); eauto.
Admitted.
      SearchAbout updateEnvironment_intermediate_big sAgentID.
 SearchAbout updateEnvironment_events sAgentID.

    
 sNumAgents_Pos_inv.
Inductive uneventfulAgentIDs {E : simEnv} :
  list (@simEvent E) -> list nat -> Prop :=
| mkUneventfulAgentIDs : 
    forall l_e l_nat,
      (forall n, In n l_nat -> (~ exists e, (In e l_e) /\ agentIDOfEvent e = n)) ->
      (forall n, (n < sNumAgents E)%nat ->
        (In n l_nat \/ (exists e, In e l_e /\ agentIDOfEvent e = n))) ->
      (NoDup l_nat) ->
  uneventfulAgentIDs l_e l_nat.



Inductive updateEnvironment_events (E : simEnv) : 
  

Lemma updateEnviornment_events (E : simEnv) :
  forall E l E',
    validSimEnv E 

Inductive updateEnvironment_movement (E : simEnv) :
  list (@simEvent E) -> simEnv -> Prop :=
| 

Lemma updateValid :
  forall E l E',
    validSimEnv E ->
    updateEnviornment_events


| mkUpdateEnvironment_events_cons :
    forall a a'
    updateEnvironment_events 
      
  Inductive updateAgent_rel_list {E: simEnv} :
    simAgent -> (list (@simEvent E)) -> simAgent -> Prop :=

  | mkUpdateAgent_rel_list_nil :
      forall a,
    updateAgent_rel_list a nil a

  | mkUpdateAgent_rel_list_cons :
      forall a a_int a_fin e l,
        updateAgent_rel a e a_int ->
        updateAgent_rel_list a_int l a_fin ->
    updateAgent_rel_list a (e::l) a_fin.



  (* functional implementation 
      **************************

  Definition updateAgent {E : simEnv} (a : simAgent) (e : @simEvent E) : simAgent :=
    match e with
    | simEvent_LB e' =>
        mkRealAgent
          (sAgentInfo a)      (* remains unchanged *)
          dRight              (* turn away from border *)
          (locationOfEvent e) (* update location of agent *)
          (sEscorting a)      (* encountering the border doesn't affect the escort list *)
          (sDestination a)    (* encountering the border doesn't affect the destination *)
          (sAgentID a)        (* remains unchanged *)

    | simEvent_UB e' =>
        mkRealAgent
          (sAgentInfo a)      (* remains unchanged *)
          dLeft               (* turn away from the border *)
          (locationOfEvent e) (* update location of agent *)
          (sEscorting a)      (* encountering the border doesn't affect the escort list *)
          (sDestination a)    (* encountering the border doesn't affect the destination *)
          (sAgentID a)        (* remains unchanged *)

    | simEvent_AE e' =>
        mkRealAgent
          (sAgentInfo a)      (* remains unchanged *)
          (directionAfterEncounterAgentEvent e') (* update direction based on location *)
          (locationOfEvent e) (* update location of agent *)
          ( (AE_ID2 e')::(sEscorting a)) (* add the encountered agent to the escort list *)      
          (sDestination a)    (* FIX ME *)
          (sAgentID a)        (* remains unchanged *)

    | simEvent_EE e' => 
        mkRealAgent
          (sAgentInfo a)      (* remains uncahnged *)
          (directionAfterEndEscortEvent e') (* update direction based on location *)             
          (locationOfEvent e) (* update location of agent *)
          nil                 (* Might need to be removed *)
          None                (* ending escort means you've reached your destination *) 
          (sAgentID a)        (* remains unchanged *)
    end.  
  *)


  

  

  (*
    This updates the environment by assigning to a new agent to the
      (agentID n) of the enviornment 
  *)
  Program Definition updateEnvironment_agent
    (E : simEnv) (n : nat) (a : simAgent) : {x : simEnv | sNumAgents x = sNumAgents E} :=
    @exist _ _
      (mkRealEnv 
        (sNumAgents E)
        (fun n' pf1 => if (n =? n') then a else (sAgents E n' pf1))
        (sPerimLength E)
        (sSpeed E)
        (sTime E))
      _.

  (* This function processes a list of events from E, updating the environment acc 
      to include the changes induced by these events *)
  Program Fixpoint updateEnvironment_events_acc
    (E acc : simEnv) (l : list (@simEvent E)) (pf : sNumAgents E = sNumAgents acc) :
  simEnv :=
    match l with
    | nil =>    acc
    | e::l' =>  updateEnvironment_events_acc
                  E 
                  (updateEnvironment_agent acc
                    (agentIDOfEvent e)
                    (sAgents acc (agentIDOfEvent e) _))
                  l'
                  _
    end.
  Next Obligation.
    apply agentIDPfOfEvent.
  Qed.

  (* updateEnvironment_events_acc only makes sense when the updates are being
      applied to the environment E *)
  Definition updateEnvironment_events E l :=
    updateEnvironment_events_acc E E l eq_refl.

  

  Lemma updateEnvironment_uniq :
    forall E1 E1' E2 E2' l l'.

  
Check (@fold_left
        simEnv
        (@simEvent E)
        (fun E e => updateEnvironment_agent
                    E
                    (agentIDOfEvent e)
                    (sAgents E (agentIDOfEvent e) (agentIDPfOfEvent e) )
        )
        l
        E).

). Check sAgents. Check
    (fun E e => updateEnvironment_agent
                  E
                  (agentIDOfEvent e)
                  (sAgents E (agentIDOfEvent e) (agentIDPfOfEvent e) )
).

  Inductive stepEnv_processEvents (E1 E2 : simEnv) (l : list (@simEvent E1)) : Prop :=
  | mkStepEnv_processEvents :
      nextEvents E1 l ->
      simEnvEQ E2 ()


        
  Check Permutation setoid.
      (* l needs to contain all possible events *)
      (* all events need to be at the least time step *)

  (* agent -> event -> agent *)
  Definition updateAgent {E : simEnv} (a : simAgent) (e : simEvent E) : simAgent :=
    match e with
    | simEvent_LB e' =>
        mkRealAgent (sAgentInfo 
    | simEvent_UB e' => (sPerimLength E)
    | simEvent_AE e' => ( (sLocation (AE_agent1 _ e')) +
                          (sLocation (AE_agent2 _ e')))/
                        (1 + 1)
    | simEvent_EE e' => EE_destination _ e'
    end.



  Inductive simEvent (a : simAgent) (E : simEnv) : Type :=
  | simLowerBorderEvent :
      forall (n : nat) (pf : (n < sNumAgents E)%nat)
             (time : Q),
             (a = sAgents E n pf) -> 
             (sHeading a = dLeft) ->
             (qDistance (sLocation a) 0) == (sSpeed E) * time ->
             (0 < time) ->
      simEvent a E
  | simUpperBorderEvent :
      forall (n : nat) (pf : (n < sNumAgents E)%nat)
             (time : Q),
             (a = sAgents E n pf) -> 
             (sHeading a = dRight) ->
             (qDistance (sLocation a) (sPerimLength E)) == (sSpeed E) * time ->
             (0 < time) ->
      simEvent a E
  | simAgentEncounterEvent :
      forall (a' : simAgent)
             (n1 n2 : nat)
             (pf1 : (n1 < sNumAgents E)%nat)
             (pf2 : (n2 < sNumAgents E)%nat)
             (time : Q),
             (a = sAgents E n1 pf1) -> 
             (a' = sAgents E n2 pf2) -> 
             (sHeading a = changeDirection (sHeading a)) ->
             (qDistance (sLocation a) (sLocation a')) ==
             (1 + 1) * (sSpeed E) * time ->
             (0 < time) ->
      simEvent a E
  | simAgentEndEscortEvent : 
      forall (n : nat) (pf : (n < sNumAgents E)%nat)
             (time : Q)
             (destination : Q),
             (sDestination a = Some destination) ->
             (directionFromSourceToTarget
               (sLocation a) (destination) (sHeading a)) ->
             (qDistance (sLocation a) 0) == (sSpeed E) * time ->
             (0 < time) ->
      simEvent a E.

  (* The location an event occurs at *)
  Definition locationOfEvent {a E} (e : simEvent a E) : Q :=
    match e with
    | simLowerBorderEvent _ _ _ _ _ _ _ => 0
    | simUpperBorderEvent _ _ _ _ _ _ _ => (sPerimLength E)
    | simAgentEncounterEvent _ _ _ _ _ _ _ _ _ _ _ => 0 
    | simAgentEndEscortEvent _ _ _ destination _ _ _ _ => destination
    end.

  Definition timeOfEvent {a E} (e : simEvent a E) : Q :=
    match e with
    | simLowerBorderEvent _ _ time _ _ _ _ => time
    | simUpperBorderEvent _ _ time _ _ _ _ => time
    | simAgentEncounterEvent _ _ _ _ _ time _ _ _ _ _ => time 
    | simAgentEndEscortEvent _ _ time _ _ _ _ _ => time
    end.

  Definition idOfEvent {a E} (e : simEvent a E) : nat :=
    match e with
    | simLowerBorderEvent n _ _ _ _ _ _ => n
    | simUpperBorderEvent n _ _ _ _ _ _ => n
    | simAgentEncounterEvent _ n _ _ _ _ _ _ _ _ _ => n 
    | simAgentEndEscortEvent n _ _ _ _ _ _ _ => n
    end.

  Definition directionOfEvent {a E time} (e : simEvent a E time) : Direction :=
    

  (* While events are parameterized by an agent, it is possible for multiple
      events to effect an agent at the same time step (e.g. if the agent
      encounters two agents involved in escorting eachother).

    Thus, our updateAgentFunction operates over a list of events rather
    than a single event.
  *)

  (*
      NB: This function is not to be used outside of the context of
          the function updateAgentByEvents, where it acts as an accumulator
  *)
  Definition updateAgentByEvents_aux {a' E time} : 
    simAgent -> simEvent a' E time -> simAgent :=
      fun a e => match e with
                  | simLowerBorderEvent _ _ _ _ _ _ =>
                      mkRealAgent
                        (sAgentInfo a)
                        dRight
                        0
                        (sEscorting a)
                        (sDestination a)
                  | simUpperBorderEvent n _ _ _ _ _ =>
                      mkRealAgent
                        (sAgentInfo a)
                        dRight
                        0
                        (sEscorting a)
                        (sDestination a)
                  | simAgentEncounterEvent _ n _ _ _ _ _ _ _ _ =>
                      mkRealAgent
                        (sAgentInfo a)
                        dRight
                        0
                        (sEscorting a)
                        (sDestination a) 
                  | simAgentEndEscortEvent n _ destination _ _ _ _ =>                      mkRealAgent
                        (sAgentInfo a)
                        dRight
                        0
                        (sEscorting a)
                        (sDestination a)
                  end.
      mkRealAgent sAgentInfo 
  Admitted.


  Definition updateAgentByEvents a {E time} (l : list (simEvent a E time)) : simAgent :=
    fold_left updateAgentByEvents_aux l a.


  Inductive SimulateEnvironment_rel : simEnv -> (list simEvent) -> simEnv -> Prop :=
  | stepWithNoEvents :
      forall E E',
        let timeDiff := (sTime E') - (sTime E) in
          forall e  
        
  
Print simLowerBorderEvent.
  Definition EnvAfterEvent : simEvent -> simEnv -> simEnv -> Prop :=
  | envAfterBorderEvent :
      forall e E E', 
        e = @simLowerBorderEvent _ _ _ _ _ _ _ _ _ ->
        
  (* A functor that lifts a function to an option type, failing if the input
      is none *)
  Definition withFail {A B : Type} (f : A -> B) : option A -> option B :=
    fun a => match a with
             | None => None
             | Some a' => Some (f a')
             end.

  (* A min function that works with option types
      returns the smallest (Some _) values of the inputs *)
  Definition QminOption (x y : option Q) : option Q :=
    match (x,y) with
    | (Some x', Some y') => Some (Qmin x' y')
    | (Some x', None) => Some x'
    | (None, Some y') => Some y'
    | (None, None) => None
    end.

  Definition QminOption3 (x y z : option Q) : option Q :=
    QminOption (QminOption x y) z.

  Definition timeToLocation (source target : Q) (speed : Q) : Q :=
    (qDistance source target)/speed.

  Definition nth_agent (n : nat) (E :simEnv) : option simAgent :=
    List.nth_error (rAgents E) n.


  (* This should be an upper bound for any event in the environment *)
  Definition eventUpperBound (E : simEnv) : Q :=
    ((rPerimLength E) + 1) / (rSpeed E).

  (********** Border Events **********)
  Definition nextBorderLocation (a : simAgent) (perimLength : Q) : Q :=
    match rHeading a with
    | dLeft => 0
    | dRight => perimLength
    end.

  (* This is the time it takes for an agent to encounter a perimeter boundry
      with its current heading and speed, provided it does so
      without interuption *)
  Definition timeToEncounterBorder (a : simAgent) (perimLength speed : Q) :=
    timeToLocation (rLocation a)
                   (nextBorderLocation a perimLength)
                   speed.

  (* Generates these times for each agent in the environment *)
  Definition Env_timeToEncounterBorder (E : simEnv) : list Q :=
    map
      (fun a => timeToEncounterBorder a (rPerimLength E) (rSpeed E))
      (rAgents E).

  (* Finds the soonest possible border event.

     -- We use QminOption to avoid the need to use the upper bound as the basis
     for the fold. This means we need to lift the ouput of Env_timeToEncounterBorder to
     an Option type*)
  Definition timeToNextBorderEvent (E : simEnv) : option Q :=
    fold_left
      QminOption
      (map Some (Env_timeToEncounterBorder E))
      None.

  (********** Encounter Events **********)

  (* Given two agent's, moving at the same speed, this is the time it
      takes for them to encounter each other (assuming no interuption).
      
    NB: This is an option in case the agents are heading in non-opposing
        directions. They may either never close the gap, or drift apart
  *)
  Definition timeToEncounterAgent (a b : simAgent) (speed : Q) : option Q :=
    match (rHeading a, rHeading b) with
    | (dLeft, dRight) => Some ((qDistance (rLocation a) (rLocation b))/(1 + 1))
    | (dRight, dLeft) => Some 0
    | (_, _) => None
    end.

  (* This is a list of all agent pairings, including agents with themselves *)
  Definition agent_pairs (E : simEnv) : list (simAgent * simAgent) :=
    list_prod (rAgents E) (rAgents E).

  (* To determine the list of agent pairs genreating encounter events,
     we filter this list to exclude the following pairs:
      1.) pairs of an agent with itself
      2.) pairs of agents already involved in an escort
  *)
  Definition encountering_agent_pairs (E : simEnv) : list (simAgent * simAgent) :=
    filter
      (fun p => (andb (* BOTH *)
        (negb (agentEqb (fst p) (snd p))) (* no irreflexive pairs *)
        (negb (agentEscortsb (fst p) (snd p))))) (* no pairs already in escort *)
      (agent_pairs E).

  Definition Env_timeToEncounterAgent (E : simEnv) : list (option Q) :=
    map
      (fun p => timeToEncounterAgent (fst p) (snd p) (rSpeed E))
      (encountering_agent_pairs E).

  (* Finds the smallest time until the next agent to agent encounter *)
  Definition timeToNextEncounterEvent (E : simEnv) : option Q :=
    fold_left QminOption (Env_timeToEncounterAgent E) None.

  
    (********** End of Escort Events **********)

  (* An end of escort event occurs when an agent reaches it's destination

      NB :  the environment invariant that agents are actually
            heading in the direction of their destination makes this work *)
  Definition timeToEndEscort (a : simAgent) (speed : Q) : option Q :=
    withFail
      (fun (dest : Q) =>(timeToLocation (rLocation a) dest speed))
      (rDestination a).

  Definition Env_timeToEndEscort (E : simEnv) : list (option Q) :=
    map (fun a => timeToEndEscort a (rSpeed E)) (rAgents E).

  Definition timeToNextEscortEvent (E : simEnv) : option Q :=
    fold_left QminOption (Env_timeToEndEscort E) None.

    (********** Calculating the next state of the environment **********)

  (* To find the next state of the environement we consider all possible
      events (border, end escort, encounter) that can occur, in isolation,
      and then compute the minimum time it takes for any of these events to
      occur. Since 
      each event as

  Definition timeToNextEvent (E : simEnv) : option Q :=
    QminOption3
      (timeToNextEscortEvent E)
      (timeToNextEncounterEvent E)
      (timeToNextBorderEvent E).
  
  Definition 


  (* Proofs re: upper bound, see if we need these:

  Lemma eventUpperBound_border :
    forall E a, In a (rAgents E) ->
      timeToEncounterBorder a (rPerimLength E) (rSpeed E) <=
      eventUpperBound E.
  Proof.
    intros.
    unfold eventUpperBound, timeToEncounterBorder, timeToLocation,
           qDistance, nextBorderLocation.
    generalize (rAgents_InPerim E _ H), (rSpeed_NotZero E). intros.
    apply Qle_shift_div_l. apply rSpeed_Positive.
  Admitted.

  Lemma eventUpperBound_timeToNextBorderEvent :
    forall E, timeToNextBorderEvent E <= eventUpperBound E.
  Proof.
    intros. 

  Admitted.
  *)

  (* The next event time is the min of all possible border/agent events *)
  Definition nextEventTime_opt (E : simEnv) : option Q :=
    QminOption (timeToNextEncounterEvent E) (timeToNextBorderEvent E).

  Lemma timeToNextBorderEvent_lt_agentTime :
    forall E a, In a (rAgents E) ->
      timeToNextBorderEvent E <=
      timeToEncounterBorder a (rPerimLength E) (rSpeed E).
  Proof.
    intros E. unfold timeToNextBorderEvent, Env_timeToEncounterBorder.
    induction (rAgents E). intros. inversion H.
    intros. destruct H as [H | H].
    + subst. simpl. unfold Qmin.
      unfold fold_left.
      admit.
    + admit.
  Admitted.

  Definition 
  



  Definition rNextBorderEvent_rel (E : RealEnv) (l : list nat) (time : R) :=
    
    
  Definition rNextBorderEvent_accum : (E : RealEnv) 

  Definition rNextBorderEvent (E : RealEnv) : (list nat * R) :=
    
*) *)
  
    