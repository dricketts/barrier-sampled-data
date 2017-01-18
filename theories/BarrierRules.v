Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import ChargeCore.Logics.ILogic.
Require Import Control.Barrier.
Require Import Control.Syntax.
Local Transparent ILInsts.ILFun_Ops.

Section BarrierRules.

  Variable state : NormedModule R_AbsRing.

  Lemma Proper_derive_barrier_dom :
    forall (G1 G2 : StateProp state) (e1 e2 : barrier state) (e1' e2' : dbarrier state),
      G1 -|- G2 ->
      |-- e1 [=] e2 ->
      derive_barrier_dom G1 e1 e1' ->
      $[G1] |-- e1' [=] e2' ->
      derive_barrier_dom G2 e2 e2'.
  Proof.
    unfold derive_barrier_dom. simpl. intros.
    apply is_derive_ext with (f:=fun t => e1 (F t)).
    { intros. auto. }
    { rewrite <- H2; auto.
      { apply H1; auto; apply H; auto. }
      { apply H; auto. } }
  Qed.

  Lemma derive_barrier_pure :
    forall (x : R) (G : StateProp state),
      derive_barrier_dom G (pure x) (pure 0).
  Proof.
    unfold derive_barrier, derive_barrier_dom, pure.
    simpl. intros. auto_derive; auto.
  Qed.

  Lemma derive_barrier_plus :
    forall (e1 e2 : barrier state) (e1' e2' : dbarrier state) (G : StateProp state),
      derive_barrier_dom G e1 e1' ->
      derive_barrier_dom G e2 e2' ->
      derive_barrier_dom G (e1 [+] e2) (e1' [+] e2').
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    specialize (H F D H1 H2 t H3). specialize (H0 F D H1 H2 t H3).
    apply (is_derive_plus _ _ _ _ _ H H0).
  Qed.

  Lemma derive_barrier_minus :
    forall (e1 e2 : barrier state) (e1' e2' : dbarrier state) (G : StateProp state),
      derive_barrier_dom G e1 e1' ->
      derive_barrier_dom G e2 e2' ->
      derive_barrier_dom G (e1 [-] e2) (e1' [-] e2').
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    specialize (H F D H1 H2 t H3). specialize (H0 F D H1 H2 t H3).
    apply (is_derive_minus _ _ _ _ _ H H0).
  Qed.

  Lemma derive_barrier_mult :
    forall (e1 e2 : barrier state) (e1' e2' : dbarrier state) (G : StateProp state),
      derive_barrier_dom G e1 e1' ->
      derive_barrier_dom G e2 e2' ->
      derive_barrier_dom G (e1 [*] e2) ((e1' [[*]] $[e2]) [+] ($[e1] [[*]] e2')).
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    specialize (H F D H1 H2 t H3). specialize (H0 F D H1 H2 t H3).
    apply (is_derive_mult _ _ _ _ _ H H0). compute. intros.
    apply Rmult_comm.
  Qed.

  Lemma derive_barrier_div :
    forall (e1 e2 : barrier state) (e1' e2' : dbarrier state) (G : StateProp state),
      derive_barrier_dom G e1 e1' ->
      derive_barrier_dom G e2 e2' ->
      G |-- e2 [<>] #0 ->
      derive_barrier_dom G (e1 [/] e2)
                         (((e1' [[*]] $[e2]) [-] ($[e1] [[*]] e2'))[[/]]($[e2][[^]]##2%nat)).
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    specialize (H F D H2 H3 t H4). specialize (H0 F D H2 H3 t H4).
    apply (is_derive_div _ _ _ _ _ H H0). apply H1; auto.
  Qed.

  Lemma derive_barrier_sqrt :
    forall (e : barrier state) (e' : dbarrier state) (G : StateProp state),
      derive_barrier_dom G e e' ->
      G |-- #0 [<] e ->
      derive_barrier_dom G ([sqrt] e) (e' [[/]](##2[[*]]([[sqrt]]$[e]))).
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    specialize (H F D H1 H2 t H3). apply (is_derive_sqrt _ _ _ H).
    apply H0; auto.
  Qed.

  Definition piecewise {T : Type} (f g : R -> T) (a : R) (k : R -> R) (x : R) :=
    if Rle_dec (k x) a then f x else g x.

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
    destruct (Rle_dec (k x) a).
    { destruct r.
      { apply (is_derive_ext_loc f).
        { apply locally_open with (D:= fun x => k x < a); auto.
          { apply (open_comp k (fun x => x < a)).
            { simpl. intros. apply H3. }
            { apply open_lt. } }
          { simpl. intros. unfold piecewise.
            destruct (Rle_dec (k x0) a); try psatzl R. reflexivity. } }
        { unfold piecewise. destruct (Rle_dec (k x) a); try psatzl R.
          apply H. assumption. } }
      { split.
        { apply is_linear_scal_l. }
        { intros x0 Hx eps. pose proof (is_filter_lim_locally_unique _ _ Hx).
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
          destruct (Rle_dec (k x0) a); try psatzl R. reflexivity. } }
      { unfold piecewise. destruct (Rle_dec (k x) a); try psatzl R.
        apply H0. psatzl R. } }
  Qed.

  Lemma derive_barrier_piecewise :
    forall (c : StateVal state R) (x : R) (e1 e2 : barrier state)
           (e1' e2' : dbarrier state) (G : StateProp state),
      derive_barrier_dom (c [<=] #x) e1 e1' ->
      derive_barrier_dom (c [>=] #x) e2 e2' ->
      $[c] [[=]] ##x |-- e1' [[=]] e2' ->
      c [=] #x |-- e1 [=] e2 ->
      (forall x, continuous c x) ->
      derive_barrier_dom G (c ?<= x [?] e1 [:] e2) ($[c] ??<= x [?] e1' [:] e2').
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    apply piecewise_is_derive
    with (k:=fun t => c (F t))
           (f:=fun t => e1 (F t))
           (g:=fun t => e2 (F t))
           (df:=fun t => e1' (D t) (F t))
           (dg:=fun t => e2' (D t) (F t)); auto.
    intros. apply continuous_comp; auto.
  Qed.

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


End BarrierRules.