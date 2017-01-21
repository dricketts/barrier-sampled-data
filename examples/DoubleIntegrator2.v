Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import ChargeCore.Logics.ILogic.
Require Import Control.Arithmetic.
Require Import Control.Barrier.
Require Import Control.Syntax.
Require Import Control.BarrierRules.
Require Import SMTC.Tactic.

Set SMT Solver "z3".
Local Transparent ILInsts.ILFun_Ops.

Section DblInt.

  (* The state of the system, position and velocity. *)
  (* Represented as a pair because Coquelicot has a NormedModule instance for pairs. *)
  Definition stateT : Type := R * R.
  Canonical state : NormedModule R_AbsRing :=
    prod_NormedModule R_AbsRing R_NormedModule R_NormedModule.
  Definition x : state -> R := fst.
  Definition v : state -> R := snd.

  (* The controller for the system. We leave it as a variable
     and impose conditions on it, rather than making it a concrete
     function. This allows one to instantiate it with anything
     satisfying those conditions. *)
  Variable u : state -> R.
  (* The maximum control magnitude. *)
  Variable umax : R.
  Hypothesis umax_gt_0 : umax > 0.
  Hypothesis umax_bounds_u : forall st, abs (u st) <= umax.
  (* The bound between sample times. *)
  Variable T : R.

  (* Some design parameters of the control constraints. *)
  Variable gamma : R.
  Hypothesis gamma_gt_0 : gamma > 0.
  Variable alpha : R.
  Hypothesis alpha_gt_0 : alpha > 0.

  (* The sampled data evolution of the system, x' = v, v' = u *)
  Definition ODE (st' st smpl : state) : Prop :=
    x st' = v st /\ v st' = u smpl.

  (* The primary barrier function for this system. *)
  (* x + umax/(2gamma^2) + v^2/(2umax^2) *)
  Definition Barrier_sqr : barrier state :=
    x [+] (#umax[*]#gamma[*]#gamma[/]#2) [+] v[*]v[/](#2[*]#umax).
  (* gamma*v + x *)
  Definition Barrier_lin : barrier state :=
    (#gamma[*]v) [+] x.
  Definition Barrier : barrier state :=
    v ?<= umax*gamma [?] Barrier_lin [:] Barrier_sqr.

  (* Derivative of the barrier function. *)
  (* x' + v*v'/umax *)
  Definition dBarrier_sqr : dbarrier state :=
    d[x] [[+]] $[v][[*]]d[v][[/]]#umax.
  (* v' + gamma*x' *)
  Definition dBarrier_lin : dbarrier state :=
    ##gamma[*]d[v] [[+]] d[x].
  Definition dBarrier : dbarrier state :=
    $[v] ??<= umax*gamma [?] dBarrier_lin [:] dBarrier_sqr.

  Lemma derive_barrier_x :
    forall (G : StateProp state),
      derive_barrier_dom G x (d[x]).
  Proof.
    unfold derive_barrier_dom. simpl. intros.
    eapply filterdiff_ext_lin.
    { apply (filterdiff_comp' F x).
      { apply H0. }
      { instantiate (1:=x). unfold x. unfold filterdiff.
        simpl. split.
        { apply is_linear_fst. }
        { intros. intro. unfold locally. exists eps.
          intros. unfold norm, minus, plus, opp. simpl.
          unfold prod_norm, prod_plus, prod_opp. simpl.
          unfold norm, minus, plus, opp. simpl.
          match goal with
          |- abs ?e <= _ => replace e with 0 by field
          end.
          pose proof (@abs_zero R_AbsRing). unfold zero in *.
          simpl in *. rewrite H4. erewrite <- Rmult_0_r.
          apply Rmult_le_compat_l.
          { destruct eps. simpl. psatzl R. }
          { apply sqrt_pos. } } } }
    { simpl. intros. reflexivity. }
  Qed.
  Lemma derive_barrier_v :
    forall (G : StateProp state),
      derive_barrier_dom G v (d[v]).
  Proof.
    unfold derive_barrier_dom. simpl. intros.
    eapply filterdiff_ext_lin.
    { apply (filterdiff_comp' F v).
      { apply H0. }
      { instantiate (1:=v). unfold v. unfold filterdiff.
        simpl. split.
        { apply is_linear_snd. }
        { intros. intro. unfold locally. exists eps.
          intros. unfold norm, minus, plus, opp. simpl.
          unfold prod_norm, prod_plus, prod_opp. simpl.
          unfold norm, minus, plus, opp. simpl.
          match goal with
          |- abs ?e <= _ => replace e with 0 by field
          end.
          pose proof (@abs_zero R_AbsRing). unfold zero in *.
          simpl in *. rewrite H4. erewrite <- Rmult_0_r.
          apply Rmult_le_compat_l.
          { destruct eps. simpl. psatzl R. }
          { apply sqrt_pos. } } } }
    { simpl. intros. reflexivity. }
  Qed.

Ltac breakAbstraction :=
  cbv beta iota delta - [Rle Rge abs Rabs].

Ltac rewrite_R0 :=
  repeat first [ rewrite Rmult_0_l
               | rewrite Rmult_0_r
               | rewrite Rplus_0_r
               | rewrite Rplus_0_l
               | rewrite Rminus_0_r 
               | rewrite Rminus_0_l ].

  Lemma dBarrier_valid :
      derive_barrier Barrier dBarrier.
  Proof.
    eapply Proper_derive_barrier_dom
    with (G1:=ltrue) (G2:=fun _ => True) (e1:=Barrier).
    { reflexivity. }
    { breakAbstraction. intros. reflexivity. }
    { unfold Barrier, Barrier_sqr, Barrier_lin.
      apply derive_barrier_piecewise.
      { auto_derive_barrier.
        { apply derive_barrier_v. }
        { apply derive_barrier_x. } }
      { auto_derive_barrier.
        { apply derive_barrier_x. }
        { simpl. intros. smt solve; apply by_z3. }
        { apply derive_barrier_v. }
        { apply derive_barrier_v. }
        { simpl. intros. psatzl R. } }
      { simpl. intros. destruct H. rewrite H0. rewrite_R0.
        unfold Rdiv at 1. rewrite_R0. field. psatzl R. }
      { simpl. intros. destruct H. rewrite H0. field. psatzl R. }
      { intros. apply continuous_snd. } }
    { unfold dBarrier, dBarrier_sqr, dBarrier_lin.
      simpl. intros. destruct (Rle_dec (v t0) (umax * gamma)).
      { rewrite_R0. field. }
      { rewrite_R0. field. psatzl R. } }
  Qed.

  Lemma continuous_dB_x :
    forall G,
      continuous_dB G ($[x]).
  Proof.
    unfold continuous_dB. simpl. intros.
    apply continuous_comp.
    { apply continuous_snd. }
    { apply continuous_fst. }
  Qed.
  Lemma continuous_dB_v :
    forall G,
      continuous_dB G ($[v]).
  Proof.
    unfold continuous_dB. simpl. intros.
    apply continuous_comp.
    { apply continuous_snd. }
    { apply continuous_snd. }
  Qed.
  Lemma continuous_dB_dx :
    forall G,
      continuous_dB G (d[x]).
  Proof.
    unfold continuous_dB. simpl. intros.
    apply continuous_comp.
    { apply continuous_fst. }
    { apply continuous_fst. }
  Qed.
  Lemma continuous_dB_dv :
    forall G,
      continuous_dB G (d[v]).
  Proof.
    unfold continuous_dB. simpl. intros.
    apply continuous_comp.
    { apply continuous_fst. }
    { apply continuous_snd. }
  Qed.

  Ltac continuous_dB_vars :=
    apply continuous_dB_x ||
    apply continuous_dB_dx ||
    apply continuous_dB_v ||
    apply continuous_dB_dv.

  (* The derivative of the barrier function is continuous. *)
  Lemma continuous_dBarrier :
    continuous_dB ltrue dBarrier.
  Proof.
    unfold dBarrier, dBarrier_sqrt, dBarrier_lin.
    apply continuous_dB_piecewise.
    { auto_continuous_dB; try continuous_dB_vars.
      { admit. }
      { admit. }
      { admit. } }
    { auto_continuous_dB; try continuous_dB_vars. }
    { admit. }
    { intros. apply continuous_fst. }
  Admitted.

  (* The relation characterizing intersample behavior of the system. *)
  Definition intersample (smpl st : state) : Prop :=
    x st <= x smpl + v smpl * T + /2*umax*T^2 /\
    v st <= v smpl + umax * T.

(*
  Lemma intersample_valid_aux :
    forall (F : trajectory state),
      solution _ (fun st' st _ => ODE st' st (F 0)) F ->
      forall t, v (F t) = v (F 0) * t.
*)

  (* The intersample relation is a valid characterization of intersample behavior. *)
  Lemma intersample_valid :
    forall (F : trajectory _) (sample : R -> R),
      solution_sampled_data ODE F sample ->
      bounded_samples sample T ->
      intersample_relation_valid intersample sample F.
  Proof.
    unfold intersample_relation_valid. intros.
  Admitted.

Goal forall (a x1 x2 y1 y2 y3 : R), x1 > 0 -> y1 > 0 ->
   y1 <= y3 ->
   a + x1 * y3 <= x2 * y2 ->
   a + x1 * y1 <= x2 * y2.
Proof.
  intros. rewrite H1; auto.
Qed.

  (* The "inductive" condition on the barrier function, i.e. its derivative
     is proportional to its value. *)
  Lemma Barrier_inductive :
      exp_condition Barrier dBarrier intersample ODE (-alpha).
  Proof.
    unfold exp_condition, Barrier, dBarrier, intersample, ODE.
    simpl. intros. destruct H0. destruct H.
    destruct (Rle_dec (x x0) (- umax / (gamma * (gamma * 1)))).
    { unfold dBarrier_sqrt, Barrier_sqrt. simpl. rewrite H0.
      rewrite H1. admit. }
    { unfold dBarrier_lin, Barrier_lin. simpl. rewrite H0.
      rewrite H1. rewrite H2 at 1; auto. rewrite <- Ropp_mult_distr_l.
      apply Ropp_le_cancel. do 2 rewrite Ropp_mult_distr_l.
      rewrite H2; try psatzl R. rewrite H; try psatzl R.
      rewrie
 rewrite H2 at 1; auto. rewrite <- H2.

Print Instances Morphisms.Proper.

rewrite H2 at 1.

  (* Invariance of the barrier region. *)
  Theorem barrier_inv :
    forall (F : trajectory _) (sample : R -> R),
      solution_sampled_data ODE F sample ->
      bounded_samples sample T ->
      trajectory_invariant F (fun st => Barrier st <= 0).
  Proof.
    intros. eapply barrier_exp_condition_sampled; eauto.
    { apply dBarrier_valid. }
    { apply continuous_dBarrier. }
    { apply intersample_valid; assumption. }
    { apply Barrier_inductive. }
  Qed.

End DblInt.