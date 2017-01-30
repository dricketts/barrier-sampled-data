Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import SMTC.Tactic.

Set SMT Solver "z3".
Local Open Scope R_scope.

Axiom by_z3 : forall (P : Prop), P.

Lemma sum_div :
  forall (a b c d : R),
    c > 0 -> d > 0 -> a > 0 -> b > 0 ->
    (a + b) / (c + d) <= (a/c) + (b/d).
Proof.
  intros. smt solve; apply by_z3.
Qed.

Lemma sum_div_denom :
  forall (a c d : R),
    c > 0 -> d > 0 -> a > 0 ->
    a / (c + d) <= (a/c) + (a/d).
Proof.
  intros. smt solve; apply by_z3.
Qed.

Lemma sum_div_num :
  forall (a b c : R),
    c <> 0 ->
    (a + b) / c = (a/c) + (b/c).
Proof.
  intros. smt solve; apply by_z3.
Qed.

Require Import Coquelicot.Coquelicot.
Require Import Coq.Logic.Classical_Prop.

Ltac breakAbstraction :=
  cbv beta iota delta - [Rle Rge abs Rabs].

Ltac rewrite_R0 :=
  repeat first [ rewrite Rmult_0_l
               | rewrite Rmult_0_r
               | rewrite Rplus_0_r
               | rewrite Rplus_0_l
               | rewrite Rminus_0_r 
               | rewrite Rminus_0_l ].

Lemma reals_dense :
  forall (x y : R),
    x < y ->
    exists z : R, x < z < y.
Proof.
  intros x y Hxy.
  pose proof (archimed (1/(y - x))).
  destruct H. clear H0.
  generalize dependent (IZR (up (1 / (y - x)))). intros n H.
  pose proof (archimed (n * x)). destruct H0.
  generalize dependent (IZR (up (n * x))). intros m H0 H1.
  exists (m / n).
  assert ((y - x) * / (y - x) = 1) by (apply Rinv_r; psatzl R).
  assert ((y - x) * n > 1).
  { unfold Rdiv in *. rewrite Rmult_1_l in *. psatz R. }
  cut (n * x < m < n * y).
  { assert (n * / n = 1) by (apply Rinv_r; psatz R).
    intros. unfold Rdiv. generalize dependent (/n). intros.
    assert (n > 0) by psatz R.
    clear - H4 H5 H6. split; psatz R. }
  { psatz R. }
Qed.
Lemma closed_continuous :
  forall {T : UniformSpace} (D : T -> Prop),
    closed D ->
    forall (f : R -> T) (u l : R),
      l < u ->
      (forall r, l <= r < u -> D (f r)) ->
      continuous f u ->
      D (f u).
Proof.
  intros. apply NNPP; intro.
  unfold closed, open, continuous, locally, filterlim,
  filter_le, filtermap in *.
  specialize (H _ H3). specialize (H2 _ H).
  simpl in *. destruct H2 as [eps H2].
  cbv beta iota zeta delta - [ not abs ] in H2.
  destruct (reals_dense (Rmax l (u - eps)) u).
  { destruct eps. simpl. unfold Rmax.
    destruct (Rle_dec l (u - pos)); psatzl R. }
  apply H2 with (y:=x) in H1; auto.
  { destruct eps. simpl in *. compute.
    destruct (Rcase_abs (x + - u)); try psatzl R.
    assert (u - pos < x).
    { revert H4. unfold Rmax. destruct (Rle_dec l (u - pos)); psatzl R. }
    psatzl R. }
  { revert H4. apply Rmax_case_strong; intros; psatzl R. }
Qed.

Require Import Coq.Classes.RelationClasses.
Require Import Setoid Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.RIneq.
Global Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Global Instance Reflexive_Rle : Reflexive Rle.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.
Global Instance Transitive_Rge : Transitive Rge.
Proof.
  red. intros. eapply Rge_trans; eauto.
Qed.

Global Instance Transitive_Rle : Transitive Rle.
Proof.
  red. intros. eapply Rle_trans; eauto.
Qed.

Local Open Scope R.

(*
  Add Parametric Relation : R Rle
      reflexivity proved by Rle_refl
      transitivity proved by Rle_trans
        as Rle_setoid_relation.*)
Definition such_that {A : Type} (P : A -> Prop) (R : relation A) :=
  fun x y => P x /\ R x y.

Global Instance Proper_Rmult_1 : Morphisms.Proper (Rle ++> such_that (fun x => x >= 0) eq ++>
                                                       Rle) Rmult.
Proof.
  red. red. red. intros. red in H0. destruct H0. rewrite H1.
  psatz R.
Qed.
Global Instance Proper_Rmult_2 : Morphisms.Proper (such_that (fun x => x >= 0) eq ++> Rle ++>
                                                             Rle) Rmult.
Proof.
  red. red. red. intros. red in H. destruct H. subst x.
  psatz R.
Qed.

Class Cond (A : Prop) := holds : A.
Hint Extern 1 (Cond ?A) =>
(* The goals coming from setoid_rewriting might contain this
spurious assumption *)
try match goal with [ H : Morphisms.apply_subrelation |- _ ] => clear H end;
  red; shelve (* This postpones the subgoal *)
       : typeclass_instances.

(** The trick: postpone the Cond subgoal but still ask for the Proper
subgoal to be resolved *)
Lemma such_that_shelve A (P : A -> Prop) R x :
  Cond (P x) ->
  Morphisms.Proper R x ->
  Morphisms.Proper (such_that P R) x.
Proof. repeat red; intuition. Qed.

Hint Extern 4 (Morphisms.Proper (such_that _ _) _) =>
class_apply such_that_shelve : typeclass_instances.
(* This is needed as the such_that_shelve lemma could apply all the
time and loop *)

Global Instance Proper_Rplus :
  Proper (Rle ==> Rle ==> Rle) Rplus.
Proof.
  red. red. red. intros. apply Rplus_le_compat ; assumption.
Qed.

Global Instance Proper_Rminus :
  Proper (Rle ==> Rle --> Rle) Rminus.
Proof.
  red. red. red. intros. unfold Rminus.
  apply Rplus_le_compat;
    [assumption | apply Ropp_le_contravar ; assumption].
Qed.
