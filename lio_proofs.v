Require Import Arith.
Require Import Bool.
Require Import List.
Require Import SfLib.
Require Export lio.

Lemma values_cannot_be_reduced : forall v t, 
  is_v_of_t v ->
  ~ (pure_reduce v t).
Proof.
  intros l t H1.
  unfold not.
  intro H2.
  induction H2.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto.


Lemma labels_cannot_be_reduced : forall l t, 
  is_l_of_t l ->
  ~ (pure_reduce l t).
Proof.
  intros l t H1.
  unfold not.
  intro H2.
  induction H2.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto.
  eauto. eauto.
Qed.

Hint Resolve labels_cannot_be_reduced.

Theorem deterministic_pure_reduce :
(*  forall x y1 y2 : t, pure_reduce x y1 -> pure_reduce x y2 -> y1 = y2. *)
  deterministic pure_reduce.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2. 
  pure_reduce_cases (induction Hy1) Case; intros y2 Hy2.
  Case "Pr_appCtx". inversion Hy2. 
   SCase "Pr_appCtx". apply IHHy1 in H2. subst. reflexivity.
   SCase "Pr_app". subst t3. subst. solve by inversion. 
  Case "Pr_app". inversion Hy2. subst t3. solve by inversion.  reflexivity.
  Case "Pr_fix". inversion Hy2. subst t5. reflexivity.
  Case "Pr_ifCtx". inversion Hy2. apply IHHy1 in H3. subst. reflexivity. 
   SCase "true". subst. inversion Hy1.
   SCase "false". subst. inversion Hy1.
  Case "Pr_ifTrue". inversion Hy2. inversion H3. reflexivity.
  Case "Pr_ifFalse". inversion Hy2. inversion H3. reflexivity.
  Case "Pr_joinCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
  Case "Pr_joinCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. inversion H3. apply H.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity.  
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity. 
  Case "Pr_joinBotL". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. reflexivity. 
   subst. apply labels_cannot_be_reduced in H5. inversion H5. apply H.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_joinBotR". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. apply H.
   subst. apply labels_cannot_be_reduced in H5. inversion H5. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinEq". inversion Hy2. apply labels_cannot_be_reduced in H5. inversion H5. apply H.
   subst. apply labels_cannot_be_reduced in H6. inversion H6. apply H0.
   subst. auto. 
   reflexivity. 
   reflexivity.
   subst. inversion H4.
   subst. inversion H4.
   reflexivity.
   subst. reflexivity.
  Case "Pr_joinAB". inversion Hy2. apply labels_cannot_be_reduced in H2. inversion H2. reflexivity.
   apply labels_cannot_be_reduced in H3. inversion H3. reflexivity.
   inversion H4.
   reflexivity.
   auto.
  Case "Pr_joinBA". inversion Hy2. apply labels_cannot_be_reduced in H2. inversion H2. reflexivity.
   apply labels_cannot_be_reduced in H3. inversion H3. reflexivity.
   inversion H4.
   reflexivity.
  Case "Pr_joinTopL". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. reflexivity.
   apply labels_cannot_be_reduced in H5. inversion H5. apply H. 
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinTopR". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. apply H.
   apply labels_cannot_be_reduced in H5. inversion H5. reflexivity.
   reflexivity.
   auto.
   reflexivity.
   reflexivity.
  Case "Pr_meetCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
  Case "Pr_meetCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. inversion H3. apply H.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity.  
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity. 
  Case "Pr_meetBotL". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. reflexivity. 
   subst. apply labels_cannot_be_reduced in H5. inversion H5. apply H.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetBotR". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. apply H.
   subst. apply labels_cannot_be_reduced in H5. inversion H5. reflexivity.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetEq". inversion Hy2. apply labels_cannot_be_reduced in H5. inversion H5. apply H.
   subst. apply labels_cannot_be_reduced in H6. inversion H6. apply H0.
   subst. auto. 
   subst. reflexivity. 
   reflexivity.
   subst. inversion H4.
   subst. inversion H4.
   subst. auto.
   reflexivity.
  Case "Pr_meetAB". inversion Hy2. apply labels_cannot_be_reduced in H2. inversion H2. reflexivity.
   apply labels_cannot_be_reduced in H3. inversion H3. reflexivity.
   inversion H4.
   reflexivity.
  Case "Pr_meetBA". inversion Hy2. apply labels_cannot_be_reduced in H2. inversion H2. reflexivity.
   apply labels_cannot_be_reduced in H3. inversion H3. reflexivity.
   inversion H4.
   reflexivity.
  Case "Pr_meetTopL". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. reflexivity.
   apply labels_cannot_be_reduced in H5. inversion H5. apply H. 
   reflexivity.
   subst. auto. 
   reflexivity.
   reflexivity.
  Case "Pr_meetTopR". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. apply H.
   apply labels_cannot_be_reduced in H5. inversion H5. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_canFlowToCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. inversion Hy1. apply H1.
  Case "Pr_canFlowToCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. inversion H3. apply H.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. apply H2.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. inversion Hy1. simpl. trivial.
  Case "Pr_canFlowToBot". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. reflexivity. 
   subst. apply labels_cannot_be_reduced in H5. inversion H5. apply H.
   reflexivity.
   reflexivity.
   auto.
  Case "Pr_canFlowToEq". inversion Hy2. apply labels_cannot_be_reduced in H5. inversion H5. apply H.
   subst. apply labels_cannot_be_reduced in H6. inversion H6. apply H0.
   subst. auto. 
   subst. reflexivity. 
   subst. inversion H4.
   subst. inversion H4.
   subst. inversion H4.
   subst. auto.
  Case "Pr_canFlowToAB". inversion Hy2. apply labels_cannot_be_reduced in H2. inversion H2. reflexivity.
   apply labels_cannot_be_reduced in H3. inversion H3. reflexivity.
   inversion H4.
   reflexivity.
  Case "Pr_canFlowToBA". inversion Hy2. apply labels_cannot_be_reduced in H2. inversion H2. reflexivity.
   apply labels_cannot_be_reduced in H3. inversion H3. reflexivity.
   inversion H4.
   reflexivity.
  Case "Pr_canFlowToTop". inversion Hy2. apply labels_cannot_be_reduced in H4. inversion H4. assumption.
   apply labels_cannot_be_reduced in H5. inversion H5. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_labelOfCtx1". inversion Hy2. subst. apply IHHy1 in H0. subst t'0. reflexivity.
    subst. inversion Hy1.
    subst. inversion Hy1.
  Case "Pr_labelOfCtx2". inversion Hy2. subst. inversion H0. 
    subst. apply IHHy1 in H2. subst t1'0. reflexivity.
    subst. apply labels_cannot_be_reduced in Hy1. contradiction. assumption.
  Case "Pr_labelOf". inversion Hy2. 
    subst. inversion H1.
    apply labels_cannot_be_reduced in H3. contradiction. assumption.
    reflexivity.
Qed.

Hint Resolve deterministic_pure_reduce.

Theorem deterministic_lio_reduce :
  deterministic lio_reduce.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2. 
  lio_reduce_cases (induction Hy1) Case; intros y2 Hy2.
  Case "LIO_return".
    inversion Hy2. reflexivity.
  Case "LIO_bindCtx".
    inversion Hy2.
    subst. apply IHHy1 in H8. inversion H8. reflexivity.
    subst.
    inversion Hy2.
    subst. inversion Hy1. 
  Case "LIO_bind".
    inversion Hy2.
    subst. inversion H7. reflexivity.
  Case "LIO_getLabel".
    inversion Hy2.
    subst. reflexivity.
  Case "LIO_getClearance".
    inversion Hy2.
    subst. reflexivity.
  Case "LIO_labelCtx".
    inversion Hy2.
    subst. 
    assert (t1' = t1'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). apply H0. apply H7.
    subst t1'0. reflexivity.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H0. inversion H0. assumption.
  Case "LIO_label".
    inversion Hy2.
    subst. 
    apply labels_cannot_be_reduced in H11. inversion H11. assumption.
    reflexivity.
  Case "LIO_unlabelCtx1".
    inversion Hy2.
    subst. 
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). apply H0. apply H6.
    subst t'0. reflexivity.
    subst. 
    inversion H0.
    subst. 
    apply labels_cannot_be_reduced in H0. inversion H0. assumption.
