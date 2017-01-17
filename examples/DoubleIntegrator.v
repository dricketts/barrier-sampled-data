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

  (* The primary barrier function for this system. *)
  Definition Barrier_aux (x v : R) : R :=
    if Rlt_dec x (-umax / gamma^2)
    then v - sqrt (-2*umax*(x + umax/(2*gamma^2)))
    else v + gamma*x.
  Definition Barrier (st : state) : R :=
    Barrier_aux (x st) (v st).
  (* Derivative of the barrier function. *)
  Definition dBarrier_aux (x' v' x v : R) : R :=
    if Rlt_dec x (-umax / gamma^2)
    then v' + umax*x'/sqrt (-2*umax*(x + umax/(2*gamma^2)))
    else v' + gamma*x'.
  Definition dBarrier (st' st : state) : R :=
    dBarrier_aux (x st') (v st') (x st) (v st).

  (* The barrier function derivative is correct. *)
  Lemma dBarrier_valid :
    derive_barrier Barrier dBarrier.
  Admitted.

  (* The derivative of the barrier function is continuous. *)
  Lemma continuous_dBarrier :
    continuous_dB dBarrier.
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
     is proportional to its value, holds. *)
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