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
  Hypothesis u_le_umax : forall st, u st <= umax.
  Hypothesis neg_umax_le_u : forall st, -umax <= u st.

  (* The bound between sample times. *)
  Variable T : R.
  Hypothesis T_gt_0 : T > 0.

  (* Some design parameters of the control constraints. *)
  Variable gamma : R.
  Hypothesis gamma_gt_0 : gamma > 0.
  Variable alpha : R.
  Hypothesis alpha_gt_0 : alpha > 0.

  (* Upper bound on u to enforce barrier invariance. *)
  Hypothesis u_barrier_constraint : forall st,
      u st <=
      if Rle_dec (v st) (umax * gamma)
      then (-1 / T * (gamma * v st + x st) - v st)/gamma
      else umax*(-1/T * (x st + umax * gamma * gamma/2 + v st * v st / (2 * umax)) - v st)/v st.

  (* The sampled data evolution of the system, x' = v, v' = u *)
  Definition ODE (st' st smpl : state) : Prop :=
    x st' = v st /\ v st' = u smpl.

  (* The primary barrier function for this system. *)
  (* x + (umax*gamma^2)/2 + v^2/(2umax^2) *)
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
  (* gamma*v' + x' *)
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
    unfold dBarrier, dBarrier_sqr, dBarrier_lin.
    apply continuous_dB_piecewise.
    { auto_continuous_dB; try continuous_dB_vars. }
    { auto_continuous_dB; try continuous_dB_vars.
      simpl. intros. psatzl R. }
    { simpl.  intros. rewrite H. field. psatzl R. }
    { intros. apply continuous_snd. }
  Qed.

  (* The relation characterizing intersample behavior of the system. *)
  Definition intersample (smpl st : state) : Prop :=
    if Rle_dec 0 (u smpl)
    then v st <= v smpl + u smpl * T
    else v st <= v smpl.

(*
  Lemma intersample_valid_aux :
    forall (F : trajectory state),
      solution _ (fun st' st _ => ODE st' st (F 0)) F ->
      forall t, v (F t) = v (F 0) * t.
*)

  (* The intersample relation is a valid characterization of intersample behavior. *)
  Lemma intersample_valid :
    forall (F : trajectory _) (sample : nat -> R),
      solution_sampled_data2 _ ODE F sample ->
      bounded_samples2 sample T ->
      intersample_relation_valid2 _ intersample sample F.
  Proof.
  Admitted.

  Lemma intersample_derive_bound :
    forall st' stk' st stk : state,
      intersample stk st ->
      ODE st' st stk -> ODE stk' stk stk ->
      dBarrier st' st <= dBarrier stk' stk + (2*umax*T + 2*gamma*umax).
  Proof.
    unfold intersample, ODE, dBarrier. simpl. intros. destruct H0.
    assert (/umax > 0) as umax_inv by (apply Rlt_gt; apply Rinv_0_lt_compat; psatzl R).
    destruct H1. destruct (Rle_dec (v st) (umax * gamma)).
    { destruct (Rle_dec (v stk) (umax * gamma)).
      { unfold dBarrier_lin. simpl. rewrite H0. rewrite H2.
        rewrite H1. rewrite H3.
        destruct (Rle_dec 0 (u stk)).
        { rewrite H. specialize (u_le_umax stk). psatz R. }
        { rewrite H. psatz R. } }
      { unfold dBarrier_lin, dBarrier_sqr. simpl. rewrite H0. rewrite H2.
        rewrite H1. rewrite H3. rewrite r. specialize (u_le_umax stk).
        rewrite u_le_umax at 1; try psatzl R. unfold Rdiv.
        rewrite <- neg_umax_le_u; try psatzl R.
        { assert (0 <= 2 * umax * T) by psatz R.
          rewrite <- H4. right. field. psatzl R. }
        { psatz R. } } }
    { destruct (Rle_dec (v stk) (umax * gamma)).
      { unfold dBarrier_lin, dBarrier_sqr. simpl. rewrite H0. rewrite H2.
        rewrite H1. rewrite H3. destruct (Rle_dec 0 (u stk)).
        { rewrite H at 1. rewrite r at 1. rewrite u_le_umax at 1; try psatzl R.
          unfold Rdiv. rewrite u_le_umax at 1; try psatzl R.
          { rewrite H at 1; try psatzl R. rewrite u_le_umax at 1; try psatzl R.
            rewrite <- neg_umax_le_u; try psatzl R. right. field. psatzl R. }
          { psatz R. } }
        { psatzl R. } }
      { unfold dBarrier_sqr. simpl. rewrite H0. rewrite H2. rewrite H1.
        replace (v st + v st * u stk / umax) with (v st*(1 + u stk / umax)) by (field; psatzl R).
        assert (1 + u stk / umax >= 0).
        { unfold Rdiv. apply Rle_ge. rewrite <- neg_umax_le_u; try psatzl R.
          right. field. psatzl R. }
        rewrite H3. destruct (Rle_dec 0 (u stk)).
        { rewrite H; auto. rewrite u_le_umax at 1; try psatzl R.
          rewrite Rmult_plus_distr_r. 
          unfold Rdiv. rewrite u_le_umax at 2; try psatzl R.
          { assert (0 <= 2 * gamma * umax) by psatz R. rewrite <- H5.
            right. field. psatzl R. }
          { psatz R. } }
        { assert (0 <= 2 * umax * T + 2 * gamma * umax) by psatz R. rewrite <- H5.
          rewrite H; auto. right. field. psatzl R. } } }
  Qed.


  (* The "inductive" condition on the barrier function, i.e. its derivative
     is proportional to its value. *)
  Lemma Barrier_inductive :
      exp_condition2 _ Barrier dBarrier ODE (-1/T).
  Proof.
    unfold exp_condition2, Barrier, dBarrier, ODE.
    simpl. intros. destruct H. specialize (u_barrier_constraint xk).
    destruct (Rle_dec (v xk) (umax * gamma)).
    { unfold dBarrier_lin, Barrier_lin. simpl. rewrite H. rewrite H0.
      admit. }
    { unfold dBarrier_sqr, Barrier_sqr. simpl. rewrite H. rewrite H0.
      admit. }
  Admitted.

  (* Invariance of the barrier region. *)
  Theorem barrier_inv :
    forall (F : trajectory _) (sample : nat -> R),
      solution_sampled_data2 _ ODE F sample ->
      well_formed_samples sample ->
      bounded_samples2 sample T ->
      forall t : R, Barrier (F 0) <= (2*umax*T + 2*gamma*umax) * T ->
                    Barrier (F t) <= (2*umax*T + 2*gamma*umax) * T.
  Proof.
    intros. eapply barrier_exp_condition_sampled2; eauto.
    { apply dBarrier_valid. }
    { apply continuous_dBarrier. }
    { apply intersample_valid; assumption. }
    { apply Barrier_inductive. }
    { apply intersample_derive_bound. }
    { psatz R. }
  Qed.

End DblInt.