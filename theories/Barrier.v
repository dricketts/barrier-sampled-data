Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILogicIso.
Require ChargeCore.Logics.ILInsts.

Section ODE.

  Variable state : NormedModule R_AbsRing.

  (* An ordinary differential inclusions is a predicate over
     derivatives and their variables. *)
  Definition ODI : Type := state -> state -> R -> Prop.

  (* A trajectory of the system is a mapping from time to state.
     We could restrict time to be nonegreal, but this probably makes
     most things messier. *)
  Definition trajectory : Type := R -> state.

  (* States that F is a solution to the ODI f with initial value x0. *)
  Definition solution (f : ODI) (F : trajectory) : Prop :=
    exists (D : R -> state),
      (forall x, continuous D x) /\
      forall (t : R),
        is_derive F t (D t) /\
        (0 <= t -> f (D t) (F t) t).

  Definition StateVal (T : Type) := state -> T.
  Definition FlowVal (T : Type) := state -> state -> T.
  Global Instance Applicative_StateVal : Applicative StateVal :=
    { pure := fun _ x => (fun _ => x)
      ; ap   := fun _ _ f x => (fun st => f st (x st)) }.
  Global Instance Applicative_FlowVal : Applicative FlowVal :=
    { pure := fun _ x => (fun _ _ => x)
      ; ap   := fun _ _ f x => (fun st st' => f st st' (x st st')) }.

  (* A barrier function maps states to scalars. *)
  Definition barrier : Type := StateVal R.
  Definition dbarrier : Type := FlowVal R.

  Definition StateProp := StateVal Prop.
  Definition FlowProp := FlowVal Prop.

  Definition derive_barrier_dom
             (dom : StateProp) (B : barrier) (dB : dbarrier) : Prop :=
    forall (F : trajectory) (D : R -> state),
      (forall t, continuous F t) ->
      (forall t, is_derive F t (D t)) ->
      (forall t, dom (F t) -> is_derive (fun t => B (F t)) t (dB (D t) (F t))).

  (* StateProp is an ILogic *)
  Global Instance ILogicOps_StateProp : ILogicOps StateProp :=
    ILogicOps_iso _ _.
  Global Instance ILogic_StateProp : ILogic StateProp := _.
  Global Instance ILogicOps_FlowProp : ILogicOps FlowProp :=
    ILogicOps_iso _ _.
  Global Instance ILogic_FlowProp : ILogic FlowProp := _.

  Require Import Coq.Classes.RelationClasses.

  Global Instance Reflexive_Rge : Reflexive Rge.
  Proof.
    red. intro. apply Req_ge. reflexivity.
  Qed.

  Definition derive_barrier := derive_barrier_dom (fun _ => True).

  (* If a system of ODEs has a solution, then that solution is continuous. *)
  Lemma solution_continuous :
    forall f F,
      solution f F ->
      forall t, continuous F t.
  Proof.
    intros. apply ex_derive_continuous. unfold solution in *.
    unfold ex_derive. destruct H. destruct H. specialize (H0 t).
    exists (x t). tauto.
  Qed.

  (* The least upper bound of a closed set is contained in the set. *)
  Lemma lub_closed_in_set :
    forall (S : R -> Prop) (m : R),
      closed S -> is_lub S m -> S m.
  Proof.
    unfold closed, open, is_lub, locally, ball. simpl.
    unfold AbsRing_ball. intros. apply NNPP. intro. specialize (H _ H1).
    destruct H.
    assert (is_upper_bound S (m - x)).
    { unfold is_upper_bound in *. intros. apply Rnot_gt_le. intro.
      destruct (Rle_dec x0 m).
      { assert (~ S x0).
        { apply H. unfold abs, minus, plus, opp. simpl.
          rewrite Rabs_left; [ psatzl R | ]. destruct r.
          { psatzl R. }
          { intuition congruence. } }
        auto. }
      { assert (x0 <= m) by (apply H0; auto). psatzl R. } }
    assert (m <= m - x).
    { apply H0; auto. }
    destruct x. simpl in *. psatzl R.
  Qed.

  Lemma exp_integral :
    forall (f df : R -> R) (a : R),
      (forall x, 0 <= x -> continuous df x) ->
      (forall x, is_derive f x (df x)) ->
      (forall x, 0 <= x -> df x <= a * f x) ->
      forall x, 0 <= x -> f x <= f 0 * exp (a * x).
  Proof.
    intros.
    assert (Derive (fun x : R => f x * exp (- a * x)) =
            fun x => df x*exp (-a*x) - (a*f x) * exp (-a*x))
      as HDerive.
    { apply functional_extensionality. intros.
      apply is_derive_unique. auto_derive.
      { unfold ex_derive. eauto. }
      { erewrite is_derive_unique; eauto. field. } }
    assert (forall x0,
               0 <= x0 ->
               continuous
                 (fun x1 : R =>
                    df x1*exp (-a*x1) - a*f x1 * exp (-a*x1)) x0)
      as Hcont.
    { intros. assert (continuous (fun x => exp (-a * x)) x0).
      { unfold continuous.
        rewrite <- (continuity_pt_filterlim
                      (fun x => exp (-a*x))).
        apply derivable_continuous. apply derivable_comp.
        { apply derivable_mult.
          { apply derivable_const. }
          { apply derivable_id. } }
        { apply derivable_exp. } }
      apply (continuous_minus
               (fun x => df x * exp (- a * x))
               (fun x => a * f x * exp (- a * x))).
      { apply (continuous_mult
                 (fun x => df x) (fun x => exp (-a * x))).
        { apply H. auto. }
        { auto. } }
      { apply (continuous_mult
                 (fun x => a * f x) (fun x => exp (-a * x))).
        { apply (continuous_mult (fun _ => a) f).
          { apply continuous_const. }
          { unfold continuous. apply (ex_derive_continuous f).
            unfold ex_derive. eauto. } }
        { auto. } } }
    assert (f x * exp (-a * x) - f 0 <= 0).
    { replace (f 0) with (f 0 * exp (-a * 0)).
      { rewrite <- (RInt_Derive (fun x => f x * exp (- a * x))).
        { replace 0 with (RInt (fun _ => 0) 0 x) at 2.
          { apply RInt_le; auto.
            { eexists. apply is_RInt_derive.
              { intros. apply Derive_correct. auto_derive.
                unfold ex_derive. eauto. }
              { intros. rewrite HDerive. apply Hcont.
                rewrite Rmin_left in *; psatzl R. } }
            { apply ex_RInt_const. }
            { intros. rewrite HDerive.
              apply Rle_minus. apply Rmult_le_compat_r.
              { left. apply exp_pos. }
              { apply H1. psatzl R. } } }
          { rewrite RInt_const. field. } }
        { intros. auto_derive. unfold ex_derive. eauto. }
        { intros. intros. rewrite HDerive. apply Hcont.
          rewrite Rmin_left in *; psatzl R. } }
      { rewrite Rmult_0_r. rewrite exp_0. field. } }
    { rewrite <- Ropp_mult_distr_l in H3. rewrite exp_Ropp in H3.
      apply Rminus_le in H3. apply Rle_div_l in H3.
      { assumption. }
      { apply exp_pos. } }
  Qed.

  Definition trajectory_invariant
             (F : trajectory) (P : StateProp) :=
    P (F 0) -> forall (t : R), 0 <= t -> P (F t).

  Theorem barrier_exp_condition :
    forall (B : barrier) (dB : dbarrier),
      derive_barrier B dB ->
      (forall t x' x,
          continuous (fun t : R => dB (x' t) (x t)) t) ->
      forall (f : ODI),
        (exists a : R, forall (x' x : state) t,
              f x' x t -> dB x' x <= a * B x) ->
        forall (F : trajectory),
          solution f F ->
          trajectory_invariant F (fun st => B st <= 0).
  Proof.
    unfold trajectory_invariant.
    intros. destruct H1 as [a H1]. destruct H2.
    assert (B (F t) <= B (F 0) * exp (a * t)).
    { apply exp_integral
      with (f:=fun t => B (F t))
             (df:=fun t => dB (x t) (F t)); auto.
      { intros. apply H; auto.
        { eapply solution_continuous. unfold solution.
          eexists. apply H2. }
        { apply H2. } }
      { intros. eapply H1. apply H2. assumption. } }
    pose proof (exp_pos (a * t)). subst. psatz R.
  Qed.

  Definition solution_sampled_data
             (f : state -> state -> state -> Prop)
             (F : trajectory) (sample : R -> R) : Prop :=
    exists (D : R -> state),
      (forall x, continuous D x) /\
      (forall (t : R),
          is_derive F t (D t)) /\
      (forall t, 0 <= t - sample t) /\
      forall t : R, f (D t) (F t) (F (sample t)).

  (* If a sampled data system of ODEs has a solution,
     then that solution is continuous. *)
  Lemma sampled_solution_continuous :
    forall f F sample,
      solution_sampled_data f F sample ->
      forall t, continuous F t.
  Proof.
    intros. apply ex_derive_continuous.
    unfold solution_sampled_data in *.
    unfold ex_derive. destruct H. exists (x t). apply H.
  Qed.

  Definition intersample_relation_valid
             (rel : state -> state -> Prop)
             (sample : R -> R) (F : trajectory) :=
    forall t, rel (F (sample t)) (F t).

  Definition exp_condition (B : barrier) (dB : dbarrier)
             (rel : state -> state -> Prop)
             (f : state -> state -> state -> Prop)
             (lambda : R) :=
    forall (x' x xb : state),
      rel xb x -> f x' x xb -> dB x' x <= lambda * B x.

  Definition continuous_dB (G : FlowProp) (dB : dbarrier) :=
    forall (p : state * state),
      G (fst p) (snd p) ->
      continuous (fun p => dB (fst p) (snd p)) p.

  Local Transparent ILInsts.ILFun_Ops.

  Theorem barrier_exp_condition_sampled :
    forall (B : barrier) (dB : dbarrier),
      derive_barrier B dB ->
      continuous_dB ltrue dB ->
      forall (f : state -> state -> state -> Prop) (F : trajectory)
             (lambda : R) (sample : R -> R)
             (rel : state -> state -> Prop),
        solution_sampled_data f F sample ->
        intersample_relation_valid rel sample F ->
        exp_condition B dB rel f lambda ->
        trajectory_invariant F (fun st => B st <= 0).
  Proof.
    unfold trajectory_invariant, intersample_relation_valid.
    intros. pose proof H1 as Hsol.
    unfold solution_sampled_data in *. destruct H1 as [D [? ?]].
    assert (B (F t) <= B (F 0) * exp (lambda * t)).
    { apply exp_integral
      with (f:=fun t => B (F t)) (df:=fun t => dB (D t) (F t));
      auto.
      { intros. eapply continuous_comp_2 in H0.
        { apply H0. }
        { auto. }
        { eapply sampled_solution_continuous; eauto. }
        { exact I. } }
      { intros. apply H; auto. intros.
        { eapply sampled_solution_continuous; eauto. }
        { apply H6. } }
      { intros. eapply H3. 2: apply H6. apply H2. } }
    pose proof (exp_pos (lambda * t)). psatz R.
  Qed.

  Definition exp_condition2 (B : barrier) (dB : dbarrier)
             (f : state -> state -> state -> Prop)
             (lambda : R) :=
    forall (x' xk : state),
      f x' xk xk -> dB x' xk <= lambda * B xk.

  Definition bounded_samples (sample : R -> R) (T : R) :=
    forall t, 0 <= t - sample t <= T.

  Definition solution_sampled_data2
             (f : state -> state -> state -> Prop)
             (F : trajectory) (sample : nat -> R) : Prop :=
    exists (D : R -> state),
      (forall x, continuous D x) /\
      (forall (t : R),
          is_derive F t (D t)) /\
      forall n : nat,
        let a := sample n in
        let b := sample (S n) in
        forall t : R, a <= t < b -> f (D t) (F t) (F a).

  (* If a sampled data system of ODEs has a solution,
     then that solution is continuous. *)
  Lemma sampled_solution_continuous2 :
    forall f F sample,
      solution_sampled_data2 f F sample ->
      forall t, continuous F t.
  Proof.
    intros. apply ex_derive_continuous.
    unfold solution_sampled_data in *.
    unfold ex_derive. destruct H. exists (x t). apply H.
  Qed.

  Definition well_formed_samples (sample : nat -> R) :=
    sample 0%nat = 0 /\
    (forall n : nat, sample n < sample (S n)) /\
    (forall t : R, exists n : nat, sample n <= t < sample (S n)).

  Definition bounded_samples2 (sample : nat -> R) (T : R) :=
    forall n : nat, sample (S n) - sample n <= T.

  Definition intersample_relation_valid2
             (rel : state -> state -> Prop)
             (sample : nat -> R) (F : trajectory) :=
    forall n : nat,
      let a := sample n in
        let b := sample (S n) in
        forall t : R, a <= t < b -> rel (F a) (F t).

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

  Require Import Control.Arithmetic.
  Require Import SMTC.Tactic.
  Set SMT Solver "z3".
  Theorem barrier_exp_condition_sampled2 :
    forall (B : barrier) (dB : dbarrier),
      derive_barrier B dB ->
      continuous_dB ltrue dB ->
      forall (f : state -> state -> state -> Prop) (F : trajectory)
             (sample : nat -> R) (rel : state -> state -> Prop)
             (C : R) (T : R),
        solution_sampled_data2 f F sample ->
        intersample_relation_valid2 rel sample F ->
        exp_condition2 B dB f (-1/T) ->
        (forall (x' xk' x xk : state),
            rel xk x -> f x' x xk -> f xk' xk xk -> dB x' x <= dB xk' xk + C) ->
        well_formed_samples sample ->
        bounded_samples2 sample T ->
        forall (HC : C > 0) (HT : T > 0),
        forall t : R, B (F 0) <= C * T -> B (F t) <= C * T.
  Proof.
    intros. pose proof H1 as Hsol. destruct H1 as [D [? ?]].
    assert (Derive (fun t => B (F t)) = fun t : R => dB (D t) (F t))
           as HDerive.
    { apply functional_extensionality. intros. apply is_derive_unique.
      apply H; auto.
      { eapply sampled_solution_continuous2; eauto. }
      { tauto. } }
    assert (forall x, continuous (fun t0 : R => dB (D t0) (F t0)) x).
    { intros. eapply continuous_comp_2 in H0.
      { apply H0. }
      { auto. }
      { eapply sampled_solution_continuous2; eauto. }
      { exact I. } }
    assert (forall n t,
               B (F t) = B (F (sample n)) +
                         RInt (fun t => dB (D t) (F t)) (sample n) t)
      as HRInt1.
    { intros. rewrite <- HDerive. rewrite RInt_Derive.
      { field. }
      { intros. unfold ex_derive. eexists; apply H; auto.
        { intros. eapply sampled_solution_continuous2; eauto. }
        { intros. apply H8. } }
      { intros. rewrite HDerive. auto. } }
    assert (forall n t,
               is_RInt (fun _ => (-1/T) * B (F (sample n)) + C) (sample n) t
                       ((t - sample n) * ((-1/T) * B (F (sample n)) + C))) as HRInt_val.
    { intros. apply (is_RInt_const (sample n) t0 ((-1/T) * B (F (sample n)) + C)). }
    assert (forall n t,
               sample n <= t < sample (S n) ->
               B (F t) <= B (F (sample n)) +
                          RInt (fun _ => (-1/T)*(B (F (sample n))) + C) (sample n) t)
      as RInt2.
    { intros. erewrite HRInt1. apply Rplus_le_compat_l.
      apply RInt_le.
      { tauto. }
      { eexists. apply is_RInt_derive.
        { intros. apply H; auto.
          { intros. eapply sampled_solution_continuous2; eauto. }
          { intros. apply H8. } }
        { auto. } }
      { unfold ex_RInt. eexists; eauto. }
      { intros. rewrite H4.
        { apply Rplus_le_compat_r. eapply H3. apply H8. psatzl R. }
        { apply H2. psatzl R. }
        { apply H8. psatzl R. }
        { apply H8. psatzl R. } } }
    assert (forall n,
               B (F (sample n)) <= C*T ->
               forall t,
                 sample n <= t < sample (S n) ->
                 B (F t) <= C*T) as HCT.
    { intros ? ? ? Hsmpl. specialize (RInt2 _ _ Hsmpl).
      erewrite is_RInt_unique in RInt2; eauto.
      assert (0 <= t0 - sample n) by psatzl R.
      assert (t0 - sample n <= T).
      { unfold bounded_samples2 in *. specialize (H6 n).
        psatzl R. }
      rewrite RInt2.
      destruct (Rle_dec ((-1/T) * B (F (sample n)) + C) 0).
      { rewrite H10 at 1. psatz R. }
      { etransitivity.
        { apply Rplus_le_compat_l. apply Rmult_le_compat; try psatzl R; eauto.
          reflexivity. }
        { field_simplify; psatzl R. } } }
    destruct H5. destruct H10. specialize (H11 t). destruct H11 as [n Hn].
    eapply HCT; eauto. clear Hn. induction n.
    { congruence. }
    { specialize (HCT n IHn). eapply closed_continuous with (f0:=fun t => B (F t)).
      { unfold closed. eapply open_ext. 2: apply open_gt. intros.
        simpl. instantiate (1:=C * T). psatzl R. }
      { instantiate (1:=sample n). auto. }
      { auto. }
      { apply ex_derive_continuous with (f0:=fun t => B (F t)).
        eexists. apply H; auto.
        { eapply sampled_solution_continuous2; eauto. }
        { intros. apply H8. } } }
  Qed.

End ODE.

Arguments derive_barrier [_] _ _.
Arguments derive_barrier_dom [_] _ _ _.
Arguments solution_sampled_data [_] _ _ _.
Arguments trajectory_invariant [_] _ _.
Arguments intersample_relation_valid [_] _ _ _.
Arguments exp_condition [_] _ _ _ _ _.
Arguments continuous_dB [_] _ _.