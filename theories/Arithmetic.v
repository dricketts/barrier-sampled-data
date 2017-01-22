Require Import Coq.Reals.Reals.
Require Import Why3.
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
