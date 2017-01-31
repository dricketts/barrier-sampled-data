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

  Definition piecewise {T U : Type} (f g : U -> T) (a : R) (k : U -> R) (x : U) :=
    if Rle_dec (k x) a then f x else g x.

  Lemma piecewise_is_derive :
    forall (T : NormedModule R_AbsRing) (f g df dg : R -> T) (a : R) (k : R -> R) (K : R -> Prop),
    (forall x, K x -> k x <= a -> is_derive f x (df x)) ->
    (forall x, K x -> k x >= a -> is_derive g x (dg x)) ->
    (forall x, K x -> k x = a -> df x = dg x) ->
    (forall x, K x -> k x = a -> f x = g x) ->
    (forall x, continuous k x) ->
    forall x, K x -> is_derive (piecewise f g a k) x (piecewise df dg a k x).
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
          apply H; auto. } }
      { split.
        { apply is_linear_scal_l. }
        { intros x0 Hx eps. pose proof (is_filter_lim_locally_unique _ _ Hx).
          simpl. subst x0. specialize (H x H4 (or_intror H5)). specialize (H0 x H4 (or_intror H5)).
          destruct H as [? Cf]. destruct H0 as [? Cg].
          specialize (Cf _ Hx eps). specialize (Cg _ Hx eps). pose proof (filter_and _ _ Cf Cg).
          eapply filter_imp; eauto. simpl. intros. unfold piecewise.
          destruct (Rle_dec (k x) a); try psatzl R. destruct (Rle_dec (k x0) a).
          { tauto. }
          { rewrite H1; auto. rewrite H2; tauto. } } } }
    { apply (is_derive_ext_loc g).
      { apply locally_open with (D:= fun x => k x > a); try psatzl R.
        { apply (open_comp k (fun x => x > a)).
          { simpl. intros. apply H3. }
          { apply open_gt. } }
        { simpl. intros. unfold piecewise.
          destruct (Rle_dec (k x0) a); try psatzl R. reflexivity. } }
      { unfold piecewise. destruct (Rle_dec (k x) a); try psatzl R.
        apply H0; auto. psatzl R. } }
  Qed.

  Lemma derive_barrier_piecewise :
    forall (c : StateVal state R) (x : R) (e1 e2 : barrier state)
           (e1' e2' : dbarrier state) (G : StateProp state),
      derive_barrier_dom (G //\\ c [<=] #x) e1 e1' ->
      derive_barrier_dom (G //\\ c [>=] #x) e2 e2' ->
      $[G] //\\ $[c] [[=]] ##x |-- e1' [[=]] e2' ->
      G //\\ c [=] #x |-- e1 [=] e2 ->
      (forall x, continuous c x) ->
      derive_barrier_dom G (c ?<= x [?] e1 [:] e2) ($[c] ??<= x [?] e1' [:] e2').
  Proof.
    unfold derive_barrier, derive_barrier_dom. simpl. intros.
    apply piecewise_is_derive
    with (k:=fun t => c (F t))
           (f:=fun t => e1 (F t))
           (g:=fun t => e2 (F t))
           (df:=fun t => e1' (D t) (F t))
           (dg:=fun t => e2' (D t) (F t))
           (K:=fun t => G (F t)); auto.
    intros. apply continuous_comp; auto.
  Qed.

  Lemma continuous_dB_pure :
    forall (x : R) (G : FlowProp state),
      continuous_dB G (pure x).
  Proof.
    unfold continuous_dB, pure.
    simpl. intros. apply continuous_const.
  Qed.

  Lemma continuous_dB_plus :
    forall (e1 e2 : dbarrier state) (G : FlowProp state),
      continuous_dB G e1 ->
      continuous_dB G e2 ->
      continuous_dB G (e1 [+] e2).
  Proof.
    unfold continuous_dB. simpl. intros.
    specialize (H p H1). specialize (H0 p H1).
    apply (continuous_plus _ _ _ H H0).
  Qed.

  Lemma continuous_dB_minus :
    forall (e1 e2 : dbarrier state) (G : FlowProp state),
      continuous_dB G e1 ->
      continuous_dB G e2 ->
      continuous_dB G (e1 [-] e2).
  Proof.
    unfold continuous_dB. simpl. intros.
    specialize (H p H1). specialize (H0 p H1).
    apply (continuous_minus _ _ _ H H0).
  Qed.

  Lemma continuous_dB_mult :
    forall (e1 e2 : dbarrier state) (G : FlowProp state),
      continuous_dB G e1 ->
      continuous_dB G e2 ->
      continuous_dB G (e1 [*] e2).
  Proof.
    unfold continuous_dB. simpl. intros.
    specialize (H p H1). specialize (H0 p H1).
    apply (continuous_mult _ _ _ H H0).
  Qed.

  Lemma continuous_dB_div :
    forall (e1 e2 : dbarrier state) (G : FlowProp state),
      continuous_dB G e1 ->
      continuous_dB G e2 ->
      G |-- e2 [<>] #0 ->
      continuous_dB G (e1 [/] e2).
  Proof.
    unfold continuous_dB. simpl. intros.
    specialize (H p H2). specialize (H0 p H2).
    apply (continuous_mult (fun p0 => e1 (fst p0) (snd p0))
                           (fun p0 => / e2 (fst p0) (snd p0))); auto.
    unfold continuous. simpl. eapply filterlim_comp.
    { apply H0. }
    { simpl.
      replace (locally (e2 (fst p) (snd p)))
      with (Rbar_locally (e2 (fst p) (snd p))) by reflexivity.
      replace (@locally (AbsRing_UniformSpace R_AbsRing) (/ e2 (fst p) (snd p)))
              with (Rbar_locally (/ e2 (fst p) (snd p))) by reflexivity.
      apply filterlim_Rbar_inv. apply Rbar_finite_neq. auto. }
  Qed.

  Lemma continuous_dB_sqrt :
    forall (e : dbarrier state) (G : FlowProp state),
      continuous_dB G e ->
      G |-- #0 [<] e ->
      continuous_dB G ([sqrt] e).
  Proof.
    unfold continuous_dB. simpl. intros. specialize (H p H1).
    apply continuous_comp.
    { apply H. }
    { apply continuity_pt_filterlim. apply continuity_pt_sqrt.
      specialize (H0 _ _ H1). psatzl R. }
  Qed.

  Lemma piecewise_continuous :
    forall (T U : UniformSpace)  (f g : U -> T) (a : R) (k : U -> R),
    (forall x, k x <= a -> continuous f x) ->
    (forall x, k x >= a -> continuous g x) ->
    (forall x, k x = a -> f x = g x) ->
    (forall x, continuous k x) ->
    forall x, continuous (piecewise f g a k) x.
  Proof.
    intros.
    destruct (Rle_dec (k x) a).
    { destruct r.
      { apply (continuous_ext_loc _ f).
        { apply locally_open with (D:= fun x => k x < a); auto.
          { apply (open_comp k (fun x => x < a)).
            { simpl. intros. apply H2. }
            { apply open_lt. } }
          { simpl. intros. unfold piecewise.
            destruct (Rle_dec (k x0) a); try psatzl R. reflexivity. } }
        { apply H. psatzl R. } }
      { apply filterlim_locally. intros.
        specialize (H _ (or_intror H3)). specialize (H0 _ (or_intror H3)).
        pose proof (proj1 (filterlim_locally _ _) H eps) as Cf.
        pose proof (proj1 (filterlim_locally _ _) H0 eps) as Cg.
        pose proof (filter_and _ _ Cf Cg).
        eapply filter_imp; eauto; simpl. intros. unfold piecewise.
        destruct (Rle_dec (k x) a); try psatzl R. destruct (Rle_dec (k x0) a).
        { tauto. }
        { rewrite H1; tauto. } } }
    { apply (continuous_ext_loc _ g).
      { apply locally_open with (D:= fun x => k x > a); auto.
        { apply (open_comp k (fun x => x > a)).
          { simpl. intros. apply H2. }
          { apply open_gt. } }
        { simpl. intros. unfold piecewise.
          destruct (Rle_dec (k x0) a); try psatzl R. reflexivity. }
        { psatzl R. } }
      { apply H0; psatzl R. } }
  Qed.

  Lemma continuous_dB_piecewise :
    forall (c : StateVal state R) (x : R)
           (e1 e2 : dbarrier state) (G : FlowProp state),
      continuous_dB ($[c] [[<=]] #x) e1 ->
      continuous_dB ($[c] [[>=]] #x) e2 ->
      $[c] [[=]] #x |-- e1 [[=]] e2 ->
      (forall x : state, continuous c x) ->
      continuous_dB G ($[c] ??<= x [?] e1 [:] e2).
  Proof.
    unfold continuous_dB. simpl. intros.
    apply piecewise_continuous
    with (k:=fun p => c (snd p))
           (f:=fun p => e1 (fst p) (snd p))
           (g:=fun p => e2 (fst p) (snd p)); auto.
    intros. apply continuous_comp.
    { apply continuous_snd. }
    { apply H2. }
  Qed.

End BarrierRules.

Ltac auto_derive_barrier :=
  repeat match goal with
         | [ |- derive_barrier_dom _ (#_) _ ] => apply derive_barrier_pure
         | [ |- derive_barrier_dom _ (_ [-] _) _ ] => apply derive_barrier_minus
         | [ |- derive_barrier_dom _ (_ [+] _) _ ] => apply derive_barrier_plus
         | [ |- derive_barrier_dom _ (_ [/] _) _ ] => apply derive_barrier_div
         | [ |- derive_barrier_dom _ (_ [*] _) _ ] => apply derive_barrier_mult
         | [ |- derive_barrier_dom _ ([sqrt] _) _ ] => apply derive_barrier_sqrt
         end.

Ltac auto_continuous_dB :=
  repeat match goal with
         | [ |- continuous_dB _ (#_) ] => apply continuous_dB_pure
         | [ |- continuous_dB _ (_ [-] _) ] => apply continuous_dB_minus
         | [ |- continuous_dB _ (_ [+] _) ] => apply continuous_dB_plus
         | [ |- continuous_dB _ (_ [/] _) ] => apply continuous_dB_div
         | [ |- continuous_dB _ (_ [*] _) ] => apply continuous_dB_mult
         | [ |- continuous_dB _ ([sqrt] _) ] => apply continuous_dB_sqrt
         end.

Lemma is_derive_fst :
  forall (T U : NormedModule R_AbsRing) (F : trajectory (prod_NormedModule _ T U)) D,
    (forall t : R, is_derive F t (D t)) ->
    forall t, is_derive (fun t : R => fst (F t)) t (fst (D t)).
Proof.
  intros. eapply filterdiff_ext_lin.
  { apply (filterdiff_comp' F).
    { apply H. }
    { instantiate (1:=fst). split.
      { apply is_linear_fst. }
      { intros. unfold locally. intro. exists eps.
        intros. destruct y. destruct x. simpl. unfold minus at 2.
        rewrite minus_eq_zero. rewrite norm_zero. rewrite <- norm_ge_0.
        psatz R. destruct eps. simpl. psatzl R. } } }
  { simpl. intros. reflexivity. }
Qed.
Lemma derive_barrier_fst_R :
  forall (U : NormedModule R_AbsRing) (G : StateProp (prod_NormedModule _ R_NormedModule U)),
    derive_barrier_dom G fst (d[fst]).
Proof.
  unfold derive_barrier_dom. simpl. intros.
  apply is_derive_fst; auto.
Qed.
Lemma is_derive_snd :
  forall (T U : NormedModule R_AbsRing) (F : trajectory (prod_NormedModule _ T U)) D,
    (forall t : R, is_derive F t (D t)) ->
    forall t, is_derive (fun t : R => snd (F t)) t (snd (D t)).
Proof.
  intros. eapply filterdiff_ext_lin.
  { apply (filterdiff_comp' F).
    { apply H. }
    { instantiate (1:=snd). split.
      { apply is_linear_snd. }
      { intros. unfold locally. intro. exists eps.
        intros. destruct y. destruct x. simpl. unfold minus at 2.
        rewrite minus_eq_zero. rewrite norm_zero. rewrite <- norm_ge_0.
        psatz R. destruct eps. simpl. psatzl R. } } }
  { simpl. intros. reflexivity. }
Qed.
Lemma derive_barrier_snd_R :
  forall (U : NormedModule R_AbsRing) (G : StateProp (prod_NormedModule _ U R_NormedModule)),
    derive_barrier_dom G snd (d[snd]).
Proof.
  unfold derive_barrier_dom. simpl. intros.
  apply is_derive_snd; auto.
Qed.

Lemma continuous_dB_fst :
  forall (U : NormedModule R_AbsRing) (G : FlowProp (prod_NormedModule _ R_NormedModule U)),
    continuous_dB G ($[fst]).
Proof.
  unfold continuous_dB. simpl. intros.
  apply continuous_comp.
  { apply continuous_snd. }
  { apply continuous_fst. }
Qed.
Lemma continuous_dB_snd :
  forall (U : NormedModule R_AbsRing) (G : FlowProp (prod_NormedModule _ U R_NormedModule)),
    continuous_dB G ($[snd]).
Proof.
  unfold continuous_dB. simpl. intros.
  apply continuous_comp.
  { apply continuous_snd. }
  { apply continuous_snd. }
Qed.
Lemma continuous_dB_dfst :
  forall (U : NormedModule R_AbsRing) (G : FlowProp (prod_NormedModule _ R_NormedModule U)),
    continuous_dB G (d[fst]).
Proof.
  unfold continuous_dB. simpl. intros.
  apply continuous_comp.
  { apply continuous_fst. }
  { apply continuous_fst. }
Qed.
Lemma continuous_dB_dsnd :
  forall (U : NormedModule R_AbsRing) (G : FlowProp (prod_NormedModule _ U R_NormedModule)),
    continuous_dB G (d[snd]).
Proof.
  unfold continuous_dB. simpl. intros.
  apply continuous_comp.
  { apply continuous_fst. }
  { apply continuous_snd. }
Qed.

Ltac continuous_dB_vars :=
  apply continuous_dB_fst ||
  apply continuous_dB_dfst ||
  apply continuous_dB_snd ||
  apply continuous_dB_dsnd.
