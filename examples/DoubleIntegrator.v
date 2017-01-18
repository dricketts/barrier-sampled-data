Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import ChargeCore.Logics.ILogic.
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
  (*     v - sqrt (-2*umax*(x + umax/(2*gamma^2))) *)
  Definition Barrier_sqrt : barrier state :=
    v [-] [sqrt](#(-2)[*]#umax[*](x [+] #umax[/](#(-2)[*]#gamma[*]#gamma))).
  (* v + gamma*x *)
  Definition Barrier_lin : barrier state :=
    v [+] (#gamma[*]x).
  Definition Barrier : barrier state :=
    x ?<= -umax/gamma^2 [?] Barrier_sqrt [:] Barrier_lin.

  (* Derivative of the barrier function. *)
  (* v' + umax*x'/sqrt (-2*umax*(x + umax/(2*gamma^2))) *)
  Definition dBarrier_sqrt : dbarrier state :=
    d[v] [[+]]
    ##umax[*] d[x] [[/]]
    ([[sqrt]] (##(-2)[[*]]##umax[[*]]($[x] [[+]] ##umax[[/]](##2[[*]]##gamma[[*]]##gamma)))).
  (* v' + gamma*x' *)
  Definition dBarrier_lin : dbarrier state :=
    d[v] [[+]] (##gamma[*] d[x]).
  Definition dBarrier : dbarrier state :=
    $[x] ??<= -umax/gamma^2 [?] dBarrier_sqrt [:] dBarrier_lin.

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


Ltac auto_derive_barrier :=
  repeat match goal with
         | [ |- derive_barrier_dom _ (#_) _ ] => apply derive_barrier_pure
         | [ |- derive_barrier_dom _ (_ [-] _) _ ] => apply derive_barrier_minus
         | [ |- derive_barrier_dom _ (_ [+] _) _ ] => apply derive_barrier_plus
         | [ |- derive_barrier_dom _ (_ [/] _) _ ] => apply derive_barrier_div
         | [ |- derive_barrier_dom _ (_ [*] _) _ ] => apply derive_barrier_mult
         | [ |- derive_barrier_dom _ ([sqrt] _) _ ] => apply derive_barrier_sqrt
         end.

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
    { unfold Barrier, Barrier_sqrt, Barrier_lin.
      apply derive_barrier_piecewise.
      { auto_derive_barrier.
        { apply derive_barrier_v. }
        { apply derive_barrier_x. }
        { breakAbstraction. intros. pose proof gamma_gt_0. psatz R. }
        { breakAbstraction. intros. destruct t. admit. } }
      { auto_derive_barrier.
        { apply derive_barrier_v. }
        { apply derive_barrier_x. } }
      { simpl. intros. destruct t. destruct t0. simpl in *.
        rewrite_R0. unfold Rdiv at 2. rewrite_R0. subst r1.
        admit. }
      { admit. }
      { intros. apply continuous_fst. } }
    { admit. }
  Admitted.

  (* The derivative of the barrier function is continuous. *)
  Lemma continuous_dBarrier :
    continuous_dB dBarrier.
  Proof.
    unfold continuous_dB. intros.
    apply piecewise_continuous.
  Admitted.

  (* The relation characterizing intersample behavior of the system. *)
  Definition intersample (smpl st : state) : Prop :=
    abs (x st - x smpl) <= v smpl * T + /2*umax*T^2 /\
    abs (v st - v smpl) <= umax * T.

  (* The intersample relation is a valid characterization of intersample behavior. *)
  Lemma intersample_valid :
    forall (F : trajectory _) (sample : R -> R),
      solution_sampled_data ODE F sample ->
      bounded_samples sample T ->
      intersample_relation_valid intersample sample F.
  Admitted.

  (* The "inductive" condition on the barrier function, i.e. its derivative
     is proportional to its value. *)
  Lemma Barrier_inductive :
      exp_condition Barrier dBarrier intersample ODE (-alpha).
  Admitted.

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