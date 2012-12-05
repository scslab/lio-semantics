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

Lemma deterministic_pure_reduce :
  deterministic pure_reduce.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2. 
  pure_reduce_cases (induction Hy1) Case; intros y2 Hy2.
  Case "Pr_appCtx". inversion Hy2. 
   SCase "Pr_appCtx". apply IHHy1 in H2. subst. reflexivity.
   SCase "Pr_app". subst t3. subst. solve by inversion. 
  Case "Pr_app". inversion Hy2. subst t3. solve by inversion.  reflexivity.
  Case "Pr_fixCtx". inversion Hy2. subst t5. apply IHHy1 in H0. subst t'0. reflexivity.
    subst. inversion Hy1.
  Case "Pr_fix". inversion Hy2.  solve by inversion. reflexivity.
  Case "Pr_ifCtx". inversion Hy2. apply IHHy1 in H3. subst. reflexivity. 
   SCase "true". subst. inversion Hy1.
   SCase "false". subst. inversion Hy1.
  Case "Pr_ifTrue". inversion Hy2. solve by inversion. reflexivity.
  Case "Pr_ifFalse". inversion Hy2. solve by inversion. reflexivity.
  Case "Pr_joinCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_joinCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.  
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
  Case "Pr_joinBotL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity. 
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. assumption. 
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_joinBotR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinEq". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H6. solve by inversion. assumption.
   subst. auto. 
   reflexivity. 
   reflexivity.
   subst. solve by inversion.
   subst. solve by inversion. 
   reflexivity.
   subst. reflexivity.
  Case "Pr_joinAB". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
   auto.
  Case "Pr_joinBA". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_joinTopL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinTopR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   auto.
   reflexivity.
   reflexivity.
  Case "Pr_meetCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_meetCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.  
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity. 
  Case "Pr_meetBotL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity. 
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetBotR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetEq". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H6. solve by inversion. assumption.
   subst. auto. 
   subst. reflexivity. 
   reflexivity.
   subst. solve by inversion.
   subst. solve by inversion.
   subst. auto.
   reflexivity.
  Case "Pr_meetAB". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_meetBA". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_meetTopL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   subst. auto. 
   reflexivity.
   reflexivity.
  Case "Pr_meetTopR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_canFlowToCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_canFlowToCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
  Case "Pr_canFlowToBot". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity. 
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
  Case "Pr_canFlowToEq". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H6. solve by inversion. assumption.
   subst. auto. 
   subst. reflexivity. 
   subst. solve by inversion.
   subst. solve by inversion.
   subst. reflexivity.
  Case "Pr_canFlowToAB". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_canFlowToBA". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_canFlowToTop". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_labelOfCtx". inversion Hy2. subst. apply IHHy1 in H0. subst t'0. reflexivity.
    subst. apply values_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
  Case "Pr_labelOf". inversion Hy2. 
    subst. solve by inversion. reflexivity.
Qed.

Hint Resolve deterministic_pure_reduce.

Axiom alpha_equiv_abs_mkTo : forall l c t x x' l' c' l1,
  m_Config l c (t_Bind t (t_VAbs x  (t_MkToLabeledTCB l' c' l1 (t_Var x )))) =
  m_Config l c (t_Bind t (t_VAbs x' (t_MkToLabeledTCB l' c' l1 (t_Var x')))).

Hint Resolve alpha_equiv_abs_mkTo.

Lemma deterministic_lio_reduce :
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
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. reflexivity.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H0. solve by inversion. assumption.
  Case "LIO_label".
    inversion Hy2.
    subst. 
    apply labels_cannot_be_reduced in H. solve by inversion. assumption.
    reflexivity.
  Case "LIO_unlabelCtx".
    inversion Hy2.
    subst. 
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. reflexivity.
    subst. 
    apply values_cannot_be_reduced in H0. solve by inversion. trivial.
 Case "LIO_unlabel".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H12. solve by inversion. trivial.
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

Hint Resolve deterministic_lio_reduce.

Definition isLabel (t_6:t) : bool :=
  match t_6 with
  | t_LBot => (true)
  | t_LA => (true)
  | t_LB => (true)
  | t_LTop => (true)
  | _ => false
end.

Lemma isLabel_is_l_of_t : forall term,
  isLabel term = true <-> is_l_of_t term.
Proof.
  intros.
  induction term; simpl; eauto; try split; try reflexivity; try split; intros; try solve by inversion.
Qed.

Definition canFlowTo (l1 l2 :t) : option bool :=
  match l1 with
    | t_LBot =>  match l2 with
                 | t_LBot  => Some true
                 | t_LA    => Some true
                 | t_LB    => Some true
                 | t_LTop  => Some true
                 | _       => None
                 end
    | t_LA    =>  match l2 with
                 | t_LBot  => Some false
                 | t_LA     => Some true
                 | t_LB     => Some false
                 | t_LTop  => Some true
                 | _       => None
                 end
    | t_LB    =>  match l2 with
                 | t_LBot  => Some false
                 | t_LA     => Some false
                 | t_LB     => Some true
                 | t_LTop  => Some true
                 | _       => None
                 end
    | t_LTop =>  match l2 with
                 | t_LBot  => Some false
                 | t_LA     => Some false
                 | t_LB     => Some false
                 | t_LTop  => Some true
                 | _       => None
                 end
    | _       => None
  end.

Definition eq_option_bool (o1 o2 : option bool) : bool :=
  match o1, o2 with
    | Some x , Some y => eqb x y
    | _, _ => false
  end.

Notation " o1 '===' o2 " := (eq_option_bool o1 o2) (at level 40).

Fixpoint erase_term (l term : t) : t :=
  match term with
   | t_LBot            => t_LBot
   | t_LA              => t_LA
   | t_LB              => t_LB
   | t_LTop            => t_LTop
   | t_VTrue           => t_VTrue
   | t_VFalse          => t_VFalse
   | t_VUnit           => t_VUnit
   | t_VAbs x t5       => t_VAbs x (erase_term l t5)
   | t_VFix t5         => t_VFix (erase_term l t5)
   | t_VLIO t5         => t_VFix (erase_term l t5)
   | t_VLabeled l1 t2  => t_VLabeled l1 (if canFlowTo l1 l === Some true
                                           then erase_term l t2
                                           else t_VHole)
   | t_VHole           => t_VHole
   | t_Var x           => t_Var x
   | t_App t5 t'       => t_App (erase_term l t5) (erase_term l t')
   | t_IfEl t1 t2 t3   => t_IfEl t1 (erase_term l t2) (erase_term l t3)
   | t_Join t1 t2      => t_Join t1 t2
   | t_Meet t1 t2      => t_Meet t1 t2
   | t_CanFlowTo t1 t2 => t_CanFlowTo t1 t2
   | t_Return t5       => t_Return (erase_term l t5)
   | t_Bind t5 t'      => t_Bind (erase_term l t5) (erase_term l t')
   | t_GetLabel        => t_GetLabel
   | t_GetClearance    => t_GetClearance
   | t_LabelOf t5      => t_LabelOf (erase_term l t5)
   | t_Label t5 t'     => t_Label t5 (erase_term l t')
   | t_UnLabel t5      => t_UnLabel (erase_term l t5)
   | t_ToLabeled t1 t2 => t_ToLabeled t1 (erase_term l t2)
   | t_MkToLabeledTCB l_5 c l1 t5 => t_MkToLabeledTCB l_5 c l1 (erase_term l t5)
  end.

Definition erase_term_inv_t_VAbs : forall l x t5,
  is_l_of_t l ->
  t_VAbs x (erase_term l t5) = erase_term l (t_VAbs x t5).
Definition erase_term_inv_t_VFix : forall l t5,
  is_l_of_t l ->
  t_VFix (erase_term l t5) = erase_term l (t_VFix t5).
Definition erase_term_inv_t_VLIO : forall l t5,
  is_l_of_t l ->
  t_VLIO (erase_term l t5) = erase_term l (t_VLIO t5).
Definition erase_term_inv_t_VLabeled1 : forall l l1 t2,
  is_l_of_t l ->
  is_l_of_t l1 ->
  t_VLabeled l1 (erase_term l t2) = erase_term l (t_VLabeled l1 t2).
Definition erase_term_inv_t_VLabeled2 : forall l l1 t2,
  is_l_of_t l ->
  is_l_of_t l1 ->
  t_VLabeled l1 t_VHole = erase_term l (t_VLabeled l1 t2).
Definition erase_term_inv_t_VHole : forall l,
  is_l_of_t l ->
  t_VHole = erase_term l (t_VHole).
Definition erase_term_inv_t_App : forall l t5 t',
  is_l_of_t l ->
  t_App (erase_term l t5) (erase_term l t') = erase_term l (t_App t5 t').
Definition erase_term_inv_t_IfEl : forall l t1 t2 t3,
  is_l_of_t l ->
  t_IfEl t1 (erase_term l t2) (erase_term l t3) = erase_term l (t_IfEl t1 t2 t3).
Definition erase_term_inv_t_Return : forall l t5,
  is_l_of_t l ->
  t_Return (erase_term l t5) = erase_term l (t_Return t5).
Definition erase_term_inv_t_Bind : forall l t5 t',
  is_l_of_t l ->
  t_Bind (erase_term l t5) (erase_term l t') = erase_term l (t_Bind t5 t').
Definition erase_term_inv_t_LabelOf : forall l t5, 
  is_l_of_t l ->
  t_LabelOf (erase_term l t5) = erase_term l (t_LabelOf t5).
Definition erase_term_inv_t_Label : forall l t' t5, 
  is_l_of_t l ->
  t_Label t5 (erase_term l t') = erase_term l (t_Label t5 t').
Definition erase_term_inv_t_UnLabel : forall l t5,
  is_l_of_t l ->
  t_UnLabel (erase_term l t5) = erase_term l (t_UnLabel t5).
Definition erase_term_inv_t_ToLabeled :forall l t1 t2,
  is_l_of_t l ->
  t_ToLabeled t1 (erase_term l t2) = erase_term l (t_ToLabeled t1 t2).
Definition erase_term_inv_t_MkToLabeledTCB : forall l l_5 c l1 t5,
  is_l_of_t l ->
  is_l_of_t l_5 ->
  is_l_of_t c ->
  is_l_of_t l1 ->
  t_MkToLabeledTCB l_5 c l1 (erase_term l t5) = erase_term l (t_MkToLabeledTCB l_5 c l1 t5).

(* ~>L *)
Inductive pure_reduce_l : t -> t -> t -> Prop :=
   | pure_reduce_l_step : forall l t1 t2,
     is_l_of_t l ->
     pure_reduce t1 t2 ->
     pure_reduce_l l t1 (erase_term l t2).


Lemma deterministic_pure_reduce_l : forall l x y1 y2,
  pure_reduce_l l x y1 ->
  pure_reduce_l l x y2 ->
  y1 = y2.
Proof.
  intros l x y1 y2 Hy1 Hy2. 
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  inversion Hy2.
  assert (t2 = t3).
  Case "assertion". apply deterministic_pure_reduce with (x := t1). assumption. assumption.
  subst t3 t1.
  reflexivity.
Qed.

Definition erase_config (l : t) (cfg : m) : m :=
  match cfg with
   | m_Config l1 c1 t1 => if canFlowTo l1 l
                            then m_Config l1 c1 (erase_term l t1)
                            else m_Config l1 c1 t_VHole
  end.

Lemma erase_term_idempotent : forall l t1,
  is_l_of_t l ->
  erase_term l t1 = erase_term l (erase_term l t1).
Proof.
  intros l t1 H.
  term_cases (induction t1) Case; eauto.
  Case "term_VAbs". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VFix". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VLIO". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VLabeled". induction l; try contradiction.
    SCase "LBot". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
    SCase "LA". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_2. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
    SCase "LB". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_2. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
    SCase "LTop". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_2. reflexivity.
     simpl. rewrite <- IHt1_2. reflexivity.
     simpl. rewrite <- IHt1_2. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
  Case "term_App". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_IfEl". simpl. rewrite <- IHt1_2. rewrite <- IHt1_3. reflexivity.
  Case "term_Return". simpl. rewrite <- IHt1. reflexivity.
  Case "term_Bind". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_LabelOf". simpl. rewrite <- IHt1. reflexivity.
  Case "term_Label". simpl. rewrite <- IHt1_2. reflexivity.
  Case "term_UnLabel". simpl. rewrite <- IHt1. reflexivity.
  Case "term_ToLabeled". simpl. rewrite <- IHt1_2. reflexivity.
  Case "term_MkToLabeledTCB". simpl. rewrite <- IHt1_4. reflexivity.
Qed.

Hint Resolve erase_term_idempotent.

Lemma pure_reduce_inv : forall l t1 t2,
  is_l_of_t l ->
  pure_reduce (erase_term l t1) t2 ->
  pure_reduce_l l (erase_term l t1) (erase_term l t2).
Proof.
  intros l t1 t2 l_of_t H.
  apply pure_reduce_l_step. assumption. assumption.
Qed.

Hint Resolve pure_reduce_inv.

Lemma erase_term_homo_subst : forall l t1 x t2,
  is_l_of_t l ->
  erase_term l (tsubst_t t1 x t2) = tsubst_t (erase_term l t1) x (erase_term l t2).
Proof. Admitted.

Hint Resolve erase_term_homo_subst.

Lemma erase_hole_implies_anything: forall l l1 t1,
  is_l_of_t l ->
  is_l_of_t l1 ->
  canFlowTo l1 l = Some false ->
  erase_term l (t_VLabeled l1 t_VHole) = erase_term l (t_VLabeled l1 t1).
Proof.
  intros. simpl. rewrite H1. simpl. reflexivity.
Qed. 

Lemma erase_label_id : forall l l2,
  is_l_of_t l ->
  is_l_of_t l2 ->
  erase_term l l2 = l2.
Proof.
  intros.  induction l2; auto; inversion H0.
Qed. 

Lemma pure_reduce_simulation : forall l t1 t2,
  is_l_of_t l ->
  pure_reduce t1 t2 ->
  pure_reduce_l l (erase_term l t1) (erase_term l t2).
Proof.
  intros l t1 t2 l_of_t H.
  generalize dependent t2.
  term_cases (induction t1) Case; intros t2 H.
    Case "term_LBot". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.

    Case "term_LB". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_reduced in H. contradiction. simpl. trivial.

    Case "term_VUnit". apply values_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H. 
    Case "term_VFix". inversion H.
     SCase "fixCtx".
     admit.
     SCase "fix".
     rewrite erase_term_idempotent with (t1 := tsubst_t (t_VFix (t_VAbs x t5)) x t5).
     apply pure_reduce_l_step. assumption.
     simpl. rewrite erase_term_homo_subst.
     apply Pr_fix. assumption. assumption.
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VHole". inversion H.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
     SCase "appCtx".
     admit.
     SCase "app".  
     rewrite erase_term_idempotent with (t1 := tsubst_t t1_2 x t1).
     apply pure_reduce_l_step. assumption.
     simpl. rewrite erase_term_homo_subst.
     apply Pr_app. assumption. assumption.
    Case "term_IfEl". inversion H.
     SCase "ifCtx".
     rewrite erase_term_idempotent with (t1 := t_IfEl t1' t1_2 t1_3).  
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_ifCtx. assumption. assumption.
     SCase "ifTrue".
     rewrite erase_term_idempotent with (t1 := t2).  
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_ifTrue. assumption.
     SCase "ifFalse".
     rewrite erase_term_idempotent with (t1 := t2).  
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_ifFalse. assumption.
    Case "term_Join". simpl. apply pure_reduce_l_step. assumption. assumption.
    Case "term_Meet". simpl. apply pure_reduce_l_step. assumption. assumption.
    Case "term_CanFlowTo". simpl. apply pure_reduce_l_step. assumption. assumption.
    Case "term_Return". inversion H.
    Case "term_Bind". inversion H. 
    Case "term_GetLabel". inversion H.
    Case "term_GetClearance". inversion H.
    Case "term_LabelOf". inversion H.
     SCase "labelOfCtx".
     admit.
     SCase "labelOf". 
     rewrite erase_term_idempotent with (t1 := t2).  
     apply pure_reduce_l_step. assumption.
     subst.
     simpl. destruct (canFlowTo t2 l === Some true). 
     SSCase "true".
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. apply Pr_labelOf. assumption.
     SSCase "false".
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. apply Pr_labelOf. assumption.
     assumption.
    Case "term_Label". inversion H.
    Case "term_UnLabel". inversion H.
    Case "term_ToLabeled". inversion H.
    Case "term_MkToLabeledTCB". inversion H.
Qed.

(* -->L *)
Inductive lio_reduce_l : t -> m -> m -> Prop :=
   | lio_reduce_l_step : forall l m1 m2,
     is_l_of_t l ->
     lio_reduce m1 m2 ->
     lio_reduce_l l m1 m2.

Lemma deterministic_lio_reduce_l : forall l x y1 y2,
  lio_reduce_l l x y1 ->
  lio_reduce_l l x y2 ->
  y1 = y2.
Proof.
  intros l x y1 y2 Hy1 Hy2. 
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  inversion Hy2.
  Case "assertion". apply deterministic_lio_reduce with (x := m1). assumption. assumption.
Qed.

Hint Resolve deterministic_lio_reduce_l.


(*
Lemma erase_config_idempotent : forall l m1,
  is_l_of_t l ->
  erase_config l m1 = erase_config l (erase_config l m1).
Proof.
  Admitted.
*)
