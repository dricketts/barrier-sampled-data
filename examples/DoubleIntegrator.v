Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import Control.Barrier.

Section DblInt.

  (* The state of the system, position and velocity. *)
  (* Represented as a pair because Coquelicot has a NormedModule instance for pairs. *)
  Definition state : Type := R * R.
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
  Variable alpha : R.

  (* The sampled data evolution of the system, x' = v, v' = u *)
  Definition ODE (st' st smpl : state) : Prop :=
    x st' = v st /\ v st' = u smpl.

  (* TODO: move *)
  Definition piecewise {T : Type} (f g : R -> T) (a : R) (k : R -> R) (x : R) :=
    if Rle_dec (k x) a then f x else g x.

  (* TODO: move *)
  Lemma piecewise_is_derive :
    forall (T : NormedModule R_AbsRing) (f g df dg : R -> T) (a : R) (k : R -> R),
    (forall x, k x <= a -> is_derive f x (df x)) ->
    (forall x, k x >= a -> is_derive g x (dg x)) ->
    (forall x, k x = a -> df x = dg x) ->
    (forall x, k x = a -> f x = g x) ->
    (forall x, continuous k x) ->
    forall x, is_derive (piecewise f g a k) x (piecewise df dg a k x).
  Proof.
    intros.
    destruct (Rle_dec (k x0) a).
    { destruct r.
      { apply (is_derive_ext_loc f).
        { apply locally_open with (D:= fun x => k x < a); auto.
          { apply (open_comp k (fun x => x < a)).
            { simpl. intros. apply H3. }
            { apply open_lt. } }
          { simpl. intros. unfold piecewise.
            destruct (Rle_dec (k x1) a); try psatzl R. reflexivity. } }
        { unfold piecewise. destruct (Rle_dec (k x0) a); try psatzl R.
          apply H. assumption. } }
      { split.
        { apply is_linear_scal_l. }
        { intros x Hx eps. pose proof (is_filter_lim_locally_unique _ _ Hx).
          simpl. subst x0. specialize (H x (or_intror H4)). specialize (H0 x (or_intror H4)).
          destruct H as [? Cf]. destruct H0 as [? Cg].
          specialize (Cf _ Hx eps). specialize (Cg _ Hx eps). pose proof (filter_and _ _ Cf Cg).
          eapply filter_imp; eauto. simpl. intros. unfold piecewise.
          destruct (Rle_dec (k x) a); try psatzl R. destruct (Rle_dec (k x0) a).
          { tauto. }
          { rewrite H1; auto; rewrite H2; tauto. } } } }
    { apply (is_derive_ext_loc g).
      { apply locally_open with (D:= fun x => k x > a); try psatzl R.
        { apply (open_comp k (fun x => x > a)).
          { simpl. intros. apply H3. }
          { apply open_gt. } }
        { simpl. intros. unfold piecewise.
          destruct (Rle_dec (k x1) a); try psatzl R. reflexivity. } }
      { unfold piecewise. destruct (Rle_dec (k x0) a); try psatzl R.
        apply H0. psatzl R. } }
  Qed.

  (* The primary barrier function for this system. *)
  Definition Barrier_sqrt (x v : R) : R :=
    v - sqrt (-2*umax*(x + umax/(2*gamma^2))).
  Definition Barrier_lin (x v : R) : R :=
    v + gamma*x.
  Definition Barrier_cond (x : R) :=
    Rle_dec x (-umax / gamma^2).
  Definition Barrier_aux (x v : R) : R :=
    if Barrier_cond x
    then Barrier_sqrt x v
    else Barrier_lin x v.
  Definition Barrier (st : state) : R :=
    Barrier_aux (x st) (v st).
  (* Derivative of the barrier function. *)
  Definition dBarrier_sqrt (x' v' x : R) : R :=
    v' + umax*x'/sqrt (-2*umax*(x + umax/(2*gamma^2))).
  Definition dBarrier_lin (x' v' : R) : R :=
    v' + gamma*x'.
  Definition dBarrier_aux (x' v' x v : R) : R :=
    if Barrier_cond x
    then dBarrier_sqrt x' v' x
    else dBarrier_lin x' v'.
  Definition dBarrier (st' st : state) : R :=
    dBarrier_aux (x st') (v st') (x st) (v st).

(*
  Lemma is_derive_var_fst :
    forall (F D : R -> state),
      (forall t, is_derive F t (D t)) ->
      forall t, is_derive (fun t => fst (F t)) t (fst (D t)).
  Proof.
    simpl. unfold is_derive. unfold state. simpl. intros.
*)

  (* TODO: move *)
  Lemma piecewise_continuous :
    forall (T : NormedModule R_AbsRing) (f g : R -> T) (a : R) (k : R -> R),
    (forall x, k x <= a -> continuous f x) ->
    (forall x, k x >= a -> continuous g x) ->
    (forall x, k x = a -> f x = g x) ->
    (forall x, continuous k x) ->
    forall x, continuous (piecewise f g a k) x.
  Proof.
    intros.
    destruct (Rle_dec (k x0) a).
    { destruct r.
      { apply (continuous_ext_loc _ f).
        { apply locally_open with (D:= fun x => k x < a); auto.
          { apply (open_comp k (fun x => x < a)).
            { simpl. intros. apply H2. }
            { apply open_lt. } }
          { simpl. intros. unfold piecewise.
            destruct (Rle_dec (k x1) a); try psatzl R. reflexivity. } }
        { apply H. psatzl R. } }
      { apply filterlim_locally. intros.
        specialize (H _ (or_intror H3)). specialize (H0 _ (or_intror H3)).
        pose proof (proj1 (filterlim_locally _ _) H eps) as Cf.
        pose proof (proj1 (filterlim_locally _ _) H0 eps) as Cg.
        pose proof (filter_and _ _ Cf Cg).
        eapply filter_imp; eauto; simpl. intros. unfold piecewise.
        destruct (Rle_dec (k x0) a); try psatzl R. destruct (Rle_dec (k x1) a).
        { tauto. }
        { rewrite H1; tauto. } } }
    { apply (continuous_ext_loc _ g).
      { apply locally_open with (D:= fun x => k x > a); auto.
        { apply (open_comp k (fun x => x > a)).
          { simpl. intros. apply H2. }
          { apply open_gt. } }
        { simpl. intros. unfold piecewise.
          destruct (Rle_dec (k x1) a); try psatzl R. reflexivity. }
        { psatzl R. } }
      { apply H0; psatzl R. } }
  Qed.

  (* The barrier function derivative is correct. *)
  Lemma dBarrier_valid :
      derive_barrier Barrier dBarrier.
  Proof.
    unfold derive_barrier, Barrier, Barrier_aux, dBarrier, dBarrier_aux.
    simpl. intros.
    apply piecewise_is_derive
    with (k:=fun t => x (F t))
           (f:=fun t => Barrier_sqrt (x (F t)) (v (F t)))
           (g:=fun t => Barrier_lin (x (F t)) (v (F t)))
           (df:=fun t0 => dBarrier_sqrt (x (D t)) (v (D t)) (x (F t0)))
           (dg:=fun _ => dBarrier_lin (x (D t)) (v (D t))).
    { intros. unfold Barrier_sqrt, dBarrier_sqrt. admit. }
    { intros. unfold Barrier_lin, dBarrier_lin.
      apply is_derive_plus with (f:=fun t => v (F t)) (g:=fun t => gamma*x (F t)).
      { admit. }
      { apply is_derive_scal. admit. } }
    { intros. unfold dBarrier_sqrt, dBarrier_lin. rewrite H1. admit. }
    { intros. unfold Barrier_sqrt, Barrier_lin. rewrite H1. admit. }
    { intros. apply continuous_comp; auto. apply continuous_fst. }
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