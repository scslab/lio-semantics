Require Import Arith.
Require Import Bool.
Require Import List.
Require Import SfLib.
Require Export lio.

Lemma labels_are_values : forall l,
  is_l_of_t l ->
  is_v_of_t l.
Proof.
  intros l H.
  induction l; repeat auto.
  reflexivity.
  reflexivity.
  reflexivity.
  solve by inversion.
  solve by inversion.
  solve by inversion.
  reflexivity.
Qed.

Hint Resolve labels_are_values.

Lemma values_cannot_be_reduced : forall v t, 
  is_v_of_t v ->
  ~ (pure_reduce v t).
Proof.
  intros l t H1.
  unfold not.
  intro H2.
  induction H2; repeat eauto.
Qed.

Hint Resolve values_cannot_be_reduced.

Corollary labels_cannot_be_reduced : forall l t, 
  is_l_of_t l ->
  ~ (pure_reduce l t).
Proof.
  intros l t H1.
  eapply values_cannot_be_reduced.
  eapply labels_are_values.
  apply H1.
Qed.

Hint Resolve labels_cannot_be_reduced.

Lemma values_cannot_be_lio_reduced : forall l c v l' c' t, 
  is_v_of_t v ->
  ~ (lio_reduce (m_Config l c v) (m_Config l' c' t)).
Proof.
  intros l c v l' c' t H1.
  unfold not.
  intro H2.
  induction v; repeat (solve by inversion).
Qed.

Hint Resolve values_cannot_be_lio_reduced.

Theorem deterministic_pure_reduce :
  deterministic pure_reduce.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2. 
  pure_reduce_cases (induction Hy1) Case; intros y2 Hy2.
  Case "Pr_appCtx". inversion Hy2. 
   SCase "Pr_appCtx". apply IHHy1 in H8. subst. reflexivity.
   SCase "Pr_app". subst t3. subst. solve by inversion. 
  Case "Pr_app". inversion Hy2. subst t3. solve by inversion.  reflexivity.
  Case "Pr_fixCtx". inversion Hy2. subst t5. apply IHHy1 in H4. subst t'0. reflexivity.
    subst. inversion Hy1.
  Case "Pr_fix". inversion Hy2.  inversion H3. reflexivity.
  Case "Pr_ifCtx". inversion Hy2. apply IHHy1 in H11. subst. reflexivity. 
   SCase "true". subst. inversion Hy1.
   SCase "false". subst. inversion Hy1.
  Case "Pr_ifTrue". inversion Hy2. solve by inversion. reflexivity.
  Case "Pr_ifFalse". inversion Hy2. solve by inversion. reflexivity.
  Case "Pr_joinCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H8. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_joinCtxR". inversion Hy2. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. apply IHHy1 in H8. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.  
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
  Case "Pr_joinBotL". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity. 
   subst. apply labels_cannot_be_reduced in H7. solve by inversion. apply H.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_joinBotR". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinEq". inversion Hy2. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. auto. 
   reflexivity. 
   reflexivity.
   subst. solve by inversion.
   subst. solve by inversion. 
   reflexivity.
   subst. reflexivity.
  Case "Pr_joinAB". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
   auto.
  Case "Pr_joinBA". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_joinTopL". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H7. inversion H7. assumption.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinTopR". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   reflexivity.
   auto.
   reflexivity.
   reflexivity.
  Case "Pr_meetCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H8. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_meetCtxR". inversion Hy2. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. apply IHHy1 in H8. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.  
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
  Case "Pr_meetBotL". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity. 
   subst. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetBotR". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetEq". inversion Hy2. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. auto. 
   subst. reflexivity. 
   reflexivity.
   subst. solve by inversion.
   subst. solve by inversion.
   subst. auto.
   reflexivity.
  Case "Pr_meetAB". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_meetBA". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_meetTopL". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   reflexivity.
   subst. auto. 
   reflexivity.
   reflexivity.
  Case "Pr_meetTopR". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_canFlowToCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H8. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_canFlowToCtxR". inversion Hy2. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. apply IHHy1 in H8. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
  Case "Pr_canFlowToBot". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity. 
   subst. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
  Case "Pr_canFlowToEq". inversion Hy2. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H8. solve by inversion. assumption.
   subst. auto. 
   subst. reflexivity. 
   subst. solve by inversion.
   subst. solve by inversion.
   subst. reflexivity.
  Case "Pr_canFlowToAB". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_canFlowToBA". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_canFlowToTop". inversion Hy2. apply labels_cannot_be_reduced in H7. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H7. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_labelOfCtx". inversion Hy2. subst. apply IHHy1 in H4. subst t'0. reflexivity.
    subst. apply values_cannot_be_reduced in Hy1. solve by inversion. trivial.
  Case "Pr_labelOf". inversion Hy2. 
    subst. inversion H5. reflexivity.
Qed.

Hint Resolve deterministic_pure_reduce.


Axiom alpha_equiv_abs_mkTo : forall l c t x x' l' c' l1,
  m_Config l c (t_Bind t (t_VAbs x  (t_MkToLabeledTCB l' c' l1 (t_Var x )))) =
  m_Config l c (t_Bind t (t_VAbs x' (t_MkToLabeledTCB l' c' l1 (t_Var x')))).

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
    subst. apply IHHy1 in H14. inversion H14. reflexivity.
    subst.
    inversion Hy2.
    subst. inversion Hy1. 
  Case "LIO_bind".
    inversion Hy2.
    subst. inversion H12. reflexivity.
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
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. reflexivity.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
  Case "LIO_label".
    inversion Hy2.
    subst. 
    apply labels_cannot_be_reduced in H16. solve by inversion. assumption.
    reflexivity.
  Case "LIO_unlabelCtx".
    inversion Hy2.
    subst. 
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. reflexivity.
    subst. 
    apply values_cannot_be_reduced in H2. solve by inversion. trivial.
 Case "LIO_unlabel".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H16. solve by inversion. trivial.
    subst.
    assert (l2 = l3).
    SCase "assertion". apply deterministic_pure_reduce with (x := t_Join l_5 l1). assumption. assumption.
    subst l3. reflexivity.
  Case "LIO_toLabeled".
    inversion Hy2.
    subst.
    clear. apply alpha_equiv_abs_mkTo.
  Case "LIO_mkToLabeledTCB".
    inversion Hy2.
    reflexivity.
Qed.
    

(* with big step:
  Case "LIO_toLabeledCtx".
    inversion Hy2.
    subst.
    assert (t1' = t1'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. reflexivity.
    subst t1.
    apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
  Case "LIO_toLabeled".
    generalize dependent y2.
    induction H9.
    intros.
    subst.
    inversion Hy2.
    apply labels_cannot_be_reduced in H21. solve by inversion. assumption.
    subst.
    apply values_cannot_be_lio_multi_reduced in H9. solve by inversion. trivial.

    apply lio_multi_step with (l1 := l_5) (c1 := c) (t1 := t5) in H9.
    intros.
    subst.
    inversion Hy2.
    apply labels_cannot_be_reduced in H28. solve by inversion. assumption.
    subst.
*)
