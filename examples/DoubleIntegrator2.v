Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Tactics.Tactics.
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
  Variable umin : R.
  Hypothesis umin_gt_0 : umin > 0.
  Hypothesis u_le_umax : forall st, u st <= umax.
  Hypothesis neg_umax_le_u : forall st, -umin <= u st.

  (* The bound between sample times. *)
  Variable T : R.
  Hypothesis T_gt_0 : T > 0.

  (* Some design parameters of the control constraints. *)
  Variable gamma : R.
  Hypothesis gamma_gt_0 : gamma > 0.

  (* Upper bound on u to enforce barrier invariance. *)
  Definition u_ub (st : state) :=
    if Rle_dec (v st) (umax * gamma)
    then (-1 / T * (gamma * v st + x st) - v st)/gamma
    else umax*(-1/T * (x st + umax * gamma * gamma/2 + v st * v st / (2 * umax)) - v st)/v st.
  Hypothesis u_barrier_constraint : forall st,
      u st <= u_ub st.

  (* A relationship between the various parameters to ensure
     that a control satisfying all constraints exists. *)
  Hypothesis umax_le_f_umin : umax <= umin/(1 + 2 * T/gamma).

  (* The sampled data evolution of the system, x' = v, v' = u *)
  Definition ODE (st' st smpl : state) : Prop :=
    x st' = v st /\ v st' = u smpl.

  (* The primary barrier function for this system. *)
  (* x + (umaxc*gamma^2)/2 + v^2/(2umaxc^2) *)
  Definition Barrier_sqr : barrier state :=
    x [+] (#umax[*]#gamma[*]#gamma[/]#2) [+] v[*]v[/](#2[*]#umax).
  (* gamma*v + x *)
  Definition Barrier_lin : barrier state :=
    (#gamma[*]v) [+] x.
  Definition Barrier : barrier state :=
    v ?<= umax*gamma [?] Barrier_lin [:] Barrier_sqr.

  Definition violation := 2 * umax * T.
  Lemma zero_le_violation : 0 <= violation.
  Proof.
    unfold violation. psatz R.
  Qed.

  Lemma exists_input :
    forall st, Barrier st <= violation * T ->
                 -umin <= u_ub st.
  Proof.
    unfold Barrier, violation, u_ub. intros. destruct st as [X V]. simpl in *.
    assert (/gamma > 0) as gamma_inv by (apply Rlt_gt; apply Rinv_0_lt_compat; psatzl R).
    assert (/T > 0) as T_inv by (apply Rlt_gt; apply Rinv_0_lt_compat; psatzl R).
    destruct (Rle_dec V (umax * gamma)).
    { unfold Barrier_lin in *. simpl in *.
      transitivity ((-1 / T * 2 * umax * T * T - V) / gamma).
      { unfold Rdiv. rewrite r by psatzl R. field_simplify; try psatzl R.
        assert (-umin / (1 + 2 * T / gamma) <= -umax) by psatzl R.
        unfold Rdiv. unfold Rminus. replace (-2 * T * umax) with (2 * T * -umax) by field.
        replace (- (umax * gamma)) with (-umax * gamma) by field.
        rewrite <- H0 by psatzl R. right. field. psatzl R. }
      { unfold Rdiv. apply Rmult_le_compat_r; try psatzl R. apply Rplus_le_compat_r.
        repeat rewrite Rmult_assoc. apply Rmult_le_compat_neg_l; [ psatzl R | ].
        apply Rmult_le_compat_l; psatzl R. } }
    { unfold Barrier_sqr in *. simpl in *.
      assert (0 <= / V) as V_inv by (left; apply Rlt_gt; apply Rinv_0_lt_compat; psatz R).
      transitivity (umax * (-1 / T * 2 * umax * T * T - V) / V).
      { replace (umax * (-1 / T * 2 * umax * T * T - V) / V)
        with (2 * (- umax) * umax * T * / V + - umax) by (field; psatz R).
        assert (-umin / (1 + 2 * T / gamma) <= -umax) by psatzl R.
        rewrite <- H0; try psatzl R.
        { replace (2 * (- umin / (1 + 2 * T / gamma)) * umax * T * / V)
          with (2 * (umin / (1 + 2 * T / gamma)) * umax * T * (/ -V)) by (field; psatz R).
          assert (/( - umax * gamma) <= / - V).
          { left. apply Rinv_lt_contravar.
            { ring_simplify. repeat apply Rmult_lt_0_compat; psatz R. }
            { psatzl R. } }
          rewrite <- H1.
          { right. field. psatz R. }
          { apply Rle_ge. left. repeat (apply Rmult_lt_0_compat; [ | psatzl R]). psatzl R. } } }
      { apply Rmult_le_compat_r; auto. apply Rmult_le_compat_l; [ psatzl R | ].
        apply Rplus_le_compat_r. repeat rewrite Rmult_assoc.
        apply Rmult_le_compat_neg_l; psatzl R. } }
  Qed.

  (* Derivative of the barrier function. *)
  (* x' + v*v'/umaxc *)
  Definition dBarrier_sqr : dbarrier state :=
    d[x] [[+]] $[v][[*]]d[v][[/]]##umax.
  (* gamma*v' + x' *)
  Definition dBarrier_lin : dbarrier state :=
    ##gamma[*]d[v] [[+]] d[x].
  Definition dBarrier : dbarrier state :=
    $[v] ??<= umax*gamma [?] dBarrier_lin [:] dBarrier_sqr.

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
        { apply derive_barrier_snd_R. }
        { apply derive_barrier_fst_R. } }
      { auto_derive_barrier.
        { apply derive_barrier_fst_R. }
        { simpl. intros. psatzl R. }
        { apply derive_barrier_snd_R. }
        { apply derive_barrier_snd_R. }
        { simpl. intros. psatzl R. } }
      { simpl. intros. destruct H. rewrite H0. rewrite_R0.
        unfold Rdiv at 1. rewrite_R0. field. psatzl R. }
      { simpl. intros. destruct H. rewrite H0. field. psatzl R. }
      { intros. apply continuous_snd. } }
    { unfold dBarrier, dBarrier_sqr, dBarrier_lin.
      simpl. intros. destruct (Rle_dec (v t0) (umax * gamma)).
      { rewrite_R0. unfold v, x. reflexivity. }
      { rewrite_R0. destruct t. destruct t0. simpl. field. psatzl R. } }
  Qed.

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
    then v smpl <= v st <= v smpl + u smpl * T
    else v smpl + u smpl * T <= v st <= v smpl.

  (* The intersample relation is a valid characterization of intersample behavior. *)
  Lemma intersample_valid :
    forall (sample : nat -> R),
      bounded_samples sample T ->
      sampled_data ODE sample |--
      intersample_relation_valid2 intersample sample.
  Proof.
    intros. simpl. unfold sampled_data, intersample_relation_valid2.
    intros F Hsol n t Ht. unfold intersample. destruct Hsol as [D [Dcont [DF DFf]]].
    unfold ODE in DFf.
    assert (forall t,
               sample n <= t < sample (S n) ->
               is_derive (fun t => v (F t)) t (u (F (sample n)))) as Hderive.
    { intros. specialize (DFf n t0 H0). destruct DFf. rewrite <- H2. apply is_derive_snd; auto. }
    assert (is_RInt (fun _ => (u (F (sample n)))) (sample n) t (v (F t) - v (F (sample n)))) as HRInt.
    { apply is_RInt_derive with (f:=fun t => v (F t)).
      { intros. apply Hderive. rewrite Rmin_left in H0 by psatzl R.
        rewrite Rmax_right in H0 by psatzl R. psatzl R. }
      { intros. apply continuous_const. } }
    apply is_RInt_unique in HRInt. rewrite RInt_const in HRInt.
    destruct (Rle_dec 0 (u (F (sample n))));
      specialize (H n); psatz R.
  Qed.

  Lemma intersample_derive_bound :
    forall st' stk' st stk : state,
      intersample stk st ->
      ODE st' st stk -> ODE stk' stk stk ->
      dBarrier st' st <= Rmax (dBarrier stk' stk + violation) 0.
  Proof.
    unfold violation, intersample, ODE, dBarrier. simpl. intros. destruct H0. destruct H1.
    assert (/umax > 0) as umax_inv by (apply Rlt_gt; apply Rinv_0_lt_compat; psatzl R).
    destruct (Rle_dec (v st) (umax * gamma)).
    { destruct (Rle_dec (v stk) (umax * gamma)).
      { unfold dBarrier_lin. simpl. rewrite H0. rewrite H2.
        rewrite H1. rewrite H3. rewrite <- Rmax_l. destruct (Rle_dec 0 (u stk)).
        { destruct H. rewrite H4. rewrite u_le_umax at 2 by psatzl R. psatz R. }
        { destruct H. rewrite H4. rewrite <- zero_le_violation. psatzl R. } }
      { destruct (Rle_dec 0 (u stk)).
        { psatzl R. }
        { destruct (Rle_dec (u stk) (-umax)).
          { rewrite <- Rmax_r. unfold dBarrier_lin. simpl. rewrite H0. rewrite H2.
            rewrite r0 by psatzl R. rewrite r. psatzl R. }
          { rewrite <- Rmax_l. unfold dBarrier_lin, dBarrier_sqr. simpl. rewrite H0.
            rewrite H2. rewrite H3. rewrite H1.
            assert (gamma * u stk - v stk * u stk / umax <= umax * T).
            { replace (gamma * u stk - v stk * u stk / umax)
              with ((- u stk) * (v stk / umax - gamma)) by (field; psatzl R).
              unfold Rdiv. assert (v stk <= v st - u stk * T) by psatzl R. rewrite H4 by psatzl R.
              rewrite r by psatzl R. assert (- u stk <= umax) by psatzl R.
              unfold Rminus. replace (- (u stk * T)) with ((- u stk) * T) by field.
              rewrite H5 at 2 by psatzl R. rewrite H5.
              { field_simplify; try psatzl R. }
              { field_simplify; try psatzl R. rewrite Rmult_comm. field_simplify; try psatzl R. } }
            psatz R. } } } }
    { destruct (Rle_dec (v stk) (umax * gamma)).
      { unfold dBarrier_lin, dBarrier_sqr. simpl. rewrite H0. rewrite H2.
        rewrite H1. rewrite H3. destruct (Rle_dec 0 (u stk)).
        { rewrite <- Rmax_l. destruct H. rewrite H4 at 1.
          assert (v st * u stk / umax + u stk * T - gamma * u stk <= 2 * umax * T).
          { replace (v st * u stk / umax + u stk * T - gamma * u stk)
            with (u stk * (v st / umax + T - gamma)) by (field; psatzl R).
            unfold Rdiv. rewrite H4 by psatzl R. rewrite r by psatzl R.
            rewrite u_le_umax at 1.
            { field_simplify; try psatzl R. repeat rewrite Rdiv_1. rewrite u_le_umax by psatzl R.
              right. field. }
            { apply Rle_ge. rewrite <- r0 by psatzl R. rewrite Rmult_0_l. rewrite Rplus_0_r.
              field_simplify; psatzl R. } }
          psatzl R. }
        { psatzl R. } }
      { unfold dBarrier_sqr. simpl. rewrite H0. rewrite H1. rewrite H2. rewrite H3.
        destruct (Rle_dec 0 (u stk)).
        { rewrite <- Rmax_l. destruct H.
          replace (v st + v st * u stk / umax) with (v st * (1 + u stk / umax)) by (field; psatzl R).
          rewrite H4.
          { replace ((v stk + u stk * T) * (1 + u stk / umax))
            with (v stk + v stk * u stk / umax + u stk * T + u stk * u stk * T / umax)
              by (field; psatzl R).
            repeat rewrite Rplus_assoc. repeat apply Rplus_le_compat_l.
            rewrite u_le_umax at 1 by psatzl R. unfold Rdiv. rewrite u_le_umax at 1 by psatzl R.
            rewrite u_le_umax at 1 by psatzl R. field_simplify; psatzl R. }
          { apply Rle_ge. unfold Rdiv. rewrite <- r by psatzl R. psatzl R. } }
        { destruct (Rle_dec (u stk) (-umax)).
          { rewrite <- Rmax_r. unfold Rdiv. rewrite r by psatz R. right. field. psatzl R. }
          { rewrite <- Rmax_l.
            replace (v st + v st * u stk / umax)
            with (v st * (1 + u stk / umax)) by (field; psatzl R).
            destruct H. rewrite H4.
            { rewrite <- zero_le_violation. right. field. psatzl R.  }
            { assert (-umax <= u stk) by psatzl R. apply Rle_ge. unfold Rdiv.
              rewrite <- H5 by psatzl R. right. field. psatzl R. } } } } }
  Qed.

  (* The "inductive" condition on the barrier function, i.e. its derivative
     is proportional to its value. *)
  Lemma Barrier_inductive :
      |-- exp_condition2 _ Barrier dBarrier ODE (-1/T).
  Proof.
    unfold exp_condition2, Barrier, dBarrier, ODE, u_ub in *.
    simpl. intros x xk Blah H. destruct H. specialize (u_barrier_constraint xk).
    destruct (Rle_dec (v xk) (umax * gamma)).
    { unfold dBarrier_lin, Barrier_lin. simpl. rewrite H. rewrite H0.
      rewrite u_barrier_constraint; try psatzl R. right. field. psatzl R. }
    { unfold dBarrier_sqr, Barrier_sqr. simpl. rewrite H. rewrite H0.
      unfold Rdiv. rewrite u_barrier_constraint.
      { right. field. repeat split; try psatzl R. psatz R. }
      { psatz R. }
      { apply Rgt_lt in umax_gt_0. apply Rinv_0_lt_compat in umax_gt_0. psatzl R. } }
  Qed.

  (* Invariance of the barrier region. *)
  Theorem barrier_inv :
    forall (sample : nat -> R),
      well_formed_samples sample ->
      bounded_samples sample T ->
      sampled_data ODE sample //\\
      !(Barrier [<=] #(violation * T))
      |-- [](Barrier [<=] #(violation * T)).
  Proof.
    intros. eapply barrier_exp_condition_sampled3 with (P:=ltrue); eauto.
    { apply dBarrier_valid. }
    { apply continuous_dBarrier. }
    { charge_tauto. }
    { rewrite intersample_valid; [ charge_tauto | assumption ]. }
    { rewrite <- Barrier_inductive. charge_tauto. }
    { apply intersample_derive_bound. }
    { unfold violation. psatz R. }
    { unfold always. simpl. auto. }
    { charge_tauto. }
  Qed.

  Lemma barrier_imp_x_lt_0 :
    forall stk : state,
      $[ Barrier [<=] # (violation * T)]
       |-- exp_inductive state (fun st' st : state => ODE st' st stk)
       (x [-] # (violation * T)) (d[x] [[-]] ## 0)
       (-/gamma).
  Proof.
    unfold Barrier, Barrier_lin, Barrier_sqr, exp_inductive, ODE. simpl. intros.
    destruct H0. rewrite H0. rewrite_R0. clear - H gamma_gt_0 umax_gt_0 T_gt_0.
    destruct (Rle_dec (v t0) (umax * gamma)).
    { smt solve; apply by_z3. }
    { (*SearchAbout Rle Rge Rlt Rgt Rmult Rplus Ropp Rminus Rinv Rdiv.*)
      rewrite Rmult_comm. rewrite <- Ropp_mult_distr_r. rewrite Ropp_mult_distr_l.
      apply Rle_div_r; [ psatzl R | ]. smt solve; apply by_z3. }
  Qed.

  Theorem x_lt_0 :
    forall (sample : nat -> R),
      well_formed_samples sample ->
      bounded_samples sample T ->
      sampled_data ODE sample //\\
      !(Barrier [<=] #(violation * T)) //\\
      !(x [-] #(violation * T) [<=] #0)
      |-- [](x [-] #(violation * T) [<=] #0).
  Proof.
    intros. eapply barrier_exp_condition_sampled_weak
            with (P:=Barrier [<=] #(violation * T)) (lambda:=(-/gamma)); eauto.
    { apply derive_barrier_minus; [apply derive_barrier_fst_R | apply derive_barrier_pure]. }
    { auto_continuous_dB. apply continuous_dB_dfst. }
    { charge_tauto. }
    { apply barrier_imp_x_lt_0. }
    { rewrite <- barrier_inv; eauto. charge_tauto. }
    { charge_tauto. }
  Qed.

End DblInt.
