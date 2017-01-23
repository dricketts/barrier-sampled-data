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
  Definition ODI : Type := state -> state -> Prop.

  (* A trajectory of the system is a mapping from time to state.
     We could restrict time to be nonegreal, but this probably makes
     most things messier. *)
  Definition trajectory : Type := R -> state.

  Definition StateVal (T : Type) := state -> T.
  Definition FlowVal (T : Type) := state -> state -> T.
  Definition TrajectoryVal (T : Type) := trajectory -> T.
  Global Instance Applicative_StateVal : Applicative StateVal :=
    { pure := fun _ x => (fun _ => x)
      ; ap   := fun _ _ f x => (fun st => f st (x st)) }.
  Global Instance Applicative_FlowVal : Applicative FlowVal :=
    { pure := fun _ x => (fun _ _ => x)
      ; ap   := fun _ _ f x => (fun st st' => f st st' (x st st')) }.
  Global Instance Applicative_TrajectoryVal : Applicative TrajectoryVal :=
    { pure := fun _ x => (fun _ => x)
      ; ap   := fun _ _ f x => (fun tr => f tr (x tr)) }.

  (** Notation for applicative functors *)
  Notation "x <$> y" := (ap x y) (at level 30).

  Definition liftA1 {T U : Type} {F : Type -> Type}
             {Ap : Applicative.Applicative F}
             (f : T -> U) (x : F T) : F U := (pure f) <$> x.

  Definition liftA2 (T: Type -> Type) {app: Applicative T} (A B C: Type)
             (f: A -> B -> C) (a: T A) (b: T B): T C :=
    pure f <$> a <$> b.
  Arguments liftA2 [_ _ _ _ _] _ _ _.

  Notation "a [+] b" := (liftA2 Rplus a b) (at level 50, left associativity).
  Notation "a [-] b" := (liftA2 Rminus a b) (at level 50, left associativity).
  Notation "a [*] b" := (liftA2 Rmult a b) (at level 40, left associativity).
  Notation "a [^] n" := (liftA2 pow a n) (at level 40, left associativity).
  Notation "a [/] b" := (liftA2 Rdiv a b) (at level 40, left associativity).
  Notation "a [>=] b" := (liftA2 Rge a b) (at level 70, right associativity).
  Notation "a [<=] b" := (liftA2 Rle a b) (at level 70, right associativity).
  Notation "a [>] b" := (liftA2 Rgt a b) (at level 70, right associativity).
  Notation "a [<] b" := (liftA2 Rlt a b) (at level 70, right associativity).
  Notation "a [=] b" := (liftA2 (@eq R) a b) (at level 70, right associativity).
  Notation "a [<>] b" := (liftA1 not (liftA2 (@eq R) a b)) (at level 70, right associativity).
  Notation "[sqrt] e" := (liftA1 sqrt e) (at level 30, right associativity).
  Notation "# x" := (pure x) (at level 20, right associativity).
  Notation "c ?<= x [?] e1 [:] e2" :=
    (fun st => if Rle_dec (c st) x then e1 st else e2 st) (at level 80).

  Notation "a [[+]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rplus a b) (at level 50, left associativity).
  Notation "a [[-]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rminus a b) (at level 50, left associativity).
  Notation "a [[*]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rmult a b) (at level 40, left associativity).
  Notation "a [[^]] n" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ pow a n) (at level 40, left associativity).
  Notation "a [[/]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rdiv a b) (at level 40, left associativity).
  Notation "a [[>=]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rge a b) (at level 70, right associativity).
  Notation "a [[<=]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rle a b) (at level 70, right associativity).
  Notation "a [[>]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rgt a b) (at level 70, right associativity).
  Notation "a [[<]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ Rlt a b) (at level 70, right associativity).
  Notation "a [[=]] b" :=
    (@liftA2 _ (Applicative_FlowVal _) _ _ _ (@eq R) a b) (at level 70, right associativity).
  Notation "a [[<>]] b" :=
    (@liftA1 _ _ _ (Applicative_FlowVal _) not (@liftA2 _ (Applicative_FlowVal _) _ _ _ (@eq R) a b))
      (at level 70, right associativity).
  Notation "[[sqrt]] e" :=
    (@liftA1 _ _ _ (Applicative_FlowVal _) sqrt e) (at level 30, right associativity).
  Notation "## x" := (@pure _ (Applicative_FlowVal _) _ x) (at level 20, right associativity).
  Notation "c ??<= x [?] e1 [:] e2" :=
    (fun st' st => if Rle_dec (c st' st) x then e1 st' st else e2 st' st) (at level 80).
  Notation "'d[' x ']'" := (fun st' st => x st') (at level 20).
  Notation "'$[' e ']'" := (fun _ st => e st) (at level 20).


  Export ExtLib.Structures.Applicative.

  (* A barrier function maps states to scalars. *)
  Definition barrier : Type := StateVal R.
  Definition dbarrier : Type := FlowVal R.

  Definition StateProp := StateVal Prop.
  Definition FlowProp := FlowVal Prop.
  Definition TrajectoryProp := TrajectoryVal Prop.

  Definition always (P : StateProp) : TrajectoryProp :=
    fun F =>
      forall t : R, 0 <= t -> P (F t).

  Local Transparent ILInsts.ILFun_Ops.
  Lemma always_ltrue :
    |-- always ltrue.
  Proof.
    unfold always. simpl. auto.
  Qed.

  Definition start (P : StateProp) : TrajectoryProp :=
    fun F => P (F 0).

  Notation "[] P" := (always P) (at level 70).
  Notation "! P" := (start P) (at level 70).

  Definition derive_barrier_dom
             (dom : StateProp) (B : barrier) (dB : dbarrier) : Prop :=
    forall (F : trajectory) (D : R -> state),
      (forall t, continuous F t) ->
      (forall t, is_derive F t (D t)) ->
      (forall t, dom (F t) -> is_derive (fun t => B (F t)) t (dB (D t) (F t))).

  (* StateProp is an ILogic *)
  Global Instance ILogic_StateProp : ILogic StateProp := _.
  Global Instance ILogic_FlowProp : ILogic FlowProp := _.
  Global Instance ILogic_TrajectoryProp : ILogic TrajectoryProp := _.

  Definition derive_barrier := derive_barrier_dom (fun _ => True).

  (* States that F is a solution to the ODI f with initial value x0. *)
  Definition solution (f : ODI) : TrajectoryProp :=
    fun F =>
      exists (D : R -> state),
        (forall x, continuous D x) /\
        forall (t : R),
          is_derive F t (D t) /\
          (0 <= t -> f (D t) (F t)).

  Definition solution_bounded (f : ODI) (T : R) : TrajectoryProp :=
    fun F =>
      exists (D : R -> state),
        (forall x, continuous D x) /\
        forall (t : R),
          is_derive F t (D t) /\
          (0 <= t -> t <= T -> f (D t) (F t)).

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

  Definition exp_inductive (f : FlowProp) (B : barrier) (dB : dbarrier) (a : R) :
    FlowProp :=
    fun (x' x : state) =>
        f x' x -> dB x' x <= a * B x.

  Theorem barrier_exp_condition :
    forall (B : barrier) (dB : dbarrier),
      derive_barrier B dB ->
      (forall t x' x,
          continuous (fun t : R => dB (x' t) (x t)) t) ->
      forall (f : ODI) (a : R) (G : TrajectoryProp) (P : StateProp),
        $[P] |-- exp_inductive f B dB a ->
        G |-- solution f ->
        G |-- !(B [<=] #0) ->
        G |-- []P ->
        G |-- [](B [<=] #0).
  Proof.
    unfold always, start. simpl. intros. rename t into F.
    specialize (H2 _ H5). specialize (H3 _ H5). specialize (H4 _ H5).
    destruct H2.
    assert (B (F t0) <= B (F 0) * exp (a * t0)).
    { apply exp_integral
      with (f:=fun t => B (F t))
             (df:=fun t => dB (x t) (F t)); auto.
      { intros. apply H; auto.
        { eapply solution_continuous. unfold solution.
          eexists. apply H2. }
        { apply H2. } }
      { intros. eapply H1; [ apply H4; auto | apply H2; assumption]. } }
    pose proof (exp_pos (a * t0)). psatz R.
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

(*
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
*)

  Definition exp_condition2 (B : barrier) (dB : dbarrier)
             (f : state -> state -> state -> Prop)
             (lambda : R) : FlowProp :=
     (fun x' x => f x' x x) -->> dB [<=] $[#lambda [*] B].

  Definition sampled_data
             (f : state -> state -> state -> Prop)
             (sample : nat -> R) : TrajectoryProp :=
    fun F =>
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
      sampled_data f sample F ->
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

  Lemma well_formed_sample_ge_0 :
    forall (sample : nat -> R),
      well_formed_samples sample ->
      forall n : nat, 0 <= sample n.
  Proof.
    unfold well_formed_samples. intros. induction n.
    { psatzl R. }
    { destruct H. destruct H0. specialize (H0 n). psatzl R. }
  Qed.

  Theorem barrier_exp_condition_sampled_weak :
    forall (B : barrier) (dB : dbarrier),
      derive_barrier B dB ->
      continuous_dB ltrue dB ->
      forall (f : state -> state -> state -> Prop)
             (sample : nat -> R) (G : TrajectoryProp) (P : StateProp)
             (lambda : R),
        G |-- sampled_data f sample ->
        (forall stk, $[P] |-- exp_inductive (fun st' st => f st' st stk) B dB lambda) ->
        well_formed_samples sample ->
        G |-- []P ->
        G |-- !(B [<=] #0) ->
        G |-- [](B [<=] #0).
  Proof.
    unfold always, start. simpl. intros. rename t into F.
    specialize (H1 _ H6). specialize (H4 _ H6). specialize (H5 _ H6).
    remember H1 as Hsol.
    assert (B (F t0) <= B (F 0) * exp (lambda * t0)).
    { destruct H1.
      apply exp_integral
      with (f:=fun t => B (F t))
             (df:=fun t => dB (x t) (F t)); auto.
      { intros. eapply continuous_comp_2; eauto.
        { apply a. }
        { eapply sampled_solution_continuous2; eauto. } }
      { intros. apply H; auto.
        { eapply sampled_solution_continuous2; eauto. }
        { apply a. } }
      { intros. unfold well_formed_samples in H3. destruct H3. destruct H8.
        specialize (H9 x0). destruct H9. eapply H2; [ apply H4; auto | apply a; eauto ]. } }
    pose proof (exp_pos (lambda * t0)). psatz R.
  Qed.

  Definition bounded_samples (sample : nat -> R) (T : R) :=
    forall n : nat, sample (S n) - sample n <= T.

  Definition intersample_relation_valid2
             (rel : state -> state -> Prop)
             (sample : nat -> R) : TrajectoryProp :=
    fun F =>
      forall n : nat,
        let a := sample n in
        let b := sample (S n) in
        forall t : R, a <= t < b -> rel (F a) (F t).

  Require Import Control.Arithmetic.
  Theorem barrier_exp_condition_sampled2 :
    forall (B : barrier) (dB : dbarrier),
      derive_barrier B dB ->
      continuous_dB ltrue dB ->
      forall (f : state -> state -> state -> Prop)
             (sample : nat -> R) (rel : state -> state -> Prop)
             (C : R) (T : R) (G : TrajectoryProp) (P : StateProp),
        G |-- sampled_data f sample ->
        G |-- intersample_relation_valid2 rel sample ->
        $[P] |-- exp_condition2 B dB f (-1/T) ->
        (forall (x' xk' x xk : state),
            rel xk x -> f x' x xk -> f xk' xk xk -> dB x' x <= dB xk' xk + C) ->
        well_formed_samples sample ->
        bounded_samples sample T ->
        forall (HC : C > 0) (HT : T > 0),
        G |-- []P ->
        G |-- !(B [<=] #(C * T)) ->
        G |-- [](B [<=] #(C * T)).
  Proof.
    unfold start, always. simpl. intros. rename t into F.
    specialize (H1 _ H9). specialize (H2 _ H9).
    specialize (H7 _ H9). specialize (H8 _ H9).
    pose proof H1 as Hsol. destruct H1 as [D [? ?]].
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
        { intros. apply H11. } }
      { intros. rewrite HDerive. auto. } }
    assert (forall n t,
               is_RInt (fun _ => (-1/T) * B (F (sample n)) + C) (sample n) t
                       ((t - sample n) * ((-1/T) * B (F (sample n)) + C))) as HRInt_val.
    { intros. apply (is_RInt_const (sample n) t ((-1/T) * B (F (sample n)) + C)). }
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
          { intros. apply H11. } }
        { auto. } }
      { unfold ex_RInt. eexists; eauto. }
      { intros. rewrite H4.
        { apply Rplus_le_compat_r. eapply H3.
          { apply H7. apply well_formed_sample_ge_0; auto. }
          { apply H11. psatzl R. } }
        { apply H2. psatzl R. }
        { apply H11. psatzl R. }
        { apply H11. psatzl R. } } }
    assert (forall n,
               B (F (sample n)) <= C*T ->
               forall t,
                 sample n <= t < sample (S n) ->
                 B (F t) <= C*T) as HCT.
    { intros ? ? ? Hsmpl. specialize (RInt2 _ _ Hsmpl).
      erewrite is_RInt_unique in RInt2; eauto.
      assert (0 <= t - sample n) by psatzl R.
      assert (t - sample n <= T).
      { unfold bounded_samples in *. specialize (H6 n).
        psatzl R. }
      rewrite RInt2.
      destruct (Rle_dec ((-1/T) * B (F (sample n)) + C) 0).
      { rewrite H13 at 1. psatz R. }
      { etransitivity.
        { apply Rplus_le_compat_l. apply Rmult_le_compat; try psatzl R; eauto.
          reflexivity. }
        { field_simplify; psatzl R. } } }
    destruct H5. destruct H13. specialize (H14 t0). destruct H14 as [n Hn].
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
        { intros. apply H11. } } }
  Qed.

End ODE.

Arguments derive_barrier [_] _ _.
Arguments derive_barrier_dom [_] _ _ _.
Arguments solution_sampled_data [_] _ _ _.
Arguments intersample_relation_valid [_] _ _ _.
Arguments exp_condition [_] _ _ _ _ _.
Arguments continuous_dB [_] _ _.
Arguments sampled_data [_] _ _ _.
Arguments intersample_relation_valid2 [_] _ _ _.
Arguments start [_] _ _.
Arguments always [_] _ _.

(*
Local Transparent ILInsts.ILFun_Ops.
Lemma intersample_valid_continuous :
  forall (state : NormedModule R_AbsRing) (G : @TrajectoryProp state)
         (rel : state -> state -> Prop) (relt : state * R -> state * R -> Prop)
         (sample : nat -> R) (T : R) (f : state -> state -> state -> Prop),
    bounded_samples sample T ->
    G |-- sampled_data f sample ->
    (forall (st0 : state) (T : R),
      solution (prod_NormedModule _ state R_NormedModule)%type
               (fun st' st => snd st < T -> (f (fst st') (fst st) st0 /\ (snd st') = 1))
      |-- always (fun st => snd st < T -> relt (st0,0) st)) ->
    relt //\\ (fun st1 st2 => (snd st2) <= T) |-- (fun st1 st2 => rel (fst st1) (fst st2)) ->
    G |-- intersample_relation_valid2 rel sample.
Proof.
  simpl. intros. specialize (H0 _ H3). rename t into F.
  unfold intersample_relation_valid2. intros.
  unfold sampled_data, always in *.
  apply (H2 (F (sample n), 0) (F t, t - sample n)).
  split.
  { specialize (H1 (F (sample n)) (sample (S n) - sample n) (fun r => (F (r + sample n), r))).
    match type of H1 with
    | ?e -> _ => assert e as Hsol
    end.
    { unfold solution. destruct H0 as [D [Dcont [DF Df]]]. exists (fun x => (D (x + sample n), 1)).
      split.
      { admit. }
      { intros. split.
        { admit. }
        { intros. split.
          { apply Df. simpl in *. psatzl R. }
          { reflexivity. } } } }
    specialize (H1 Hsol (t - sample n)). simpl in *.
    replace (t - sample n + sample n) with t in H1 by psatzl R.
    apply H1.
    { psatzl R. }
    { unfold bounded_samples in *. specialize (H n). psatzl R. } }
  { simpl. unfold bounded_samples in *. specialize (H n). psatzl R. }
Admitted.
*)