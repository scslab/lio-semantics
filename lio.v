(* generated by Ott 0.21.1 from: lio.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.


Require Import SfLib.

Definition termvar := nat. (*r term variable *)
Lemma eq_termvar: forall (x y : termvar), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_termvar : ott_coq_equality.
Definition typvar := nat. (*r type variable *)
Lemma eq_typvar: forall (x y : typvar), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_typvar : ott_coq_equality.

Inductive T : Set :=  (*r type *)
 | T_TBool : T (*r Boolean *)
 | T_TUnit : T (*r unit *)
 | T_TLabel : T (*r label *)
 | T_TLIO (T5:T) (*r LIO action *)
 | T_TLabeled (T5:T) (*r labeled value *)
 | T_TVar (X:typvar) (*r variable *)
 | T_TArrow (T5:T) (T':T) (*r function *).

Inductive t : Set :=  (*r term *)
 | t_LBot : t (*r bottom *)
 | t_LA : t (*r medium-label *)
 | t_LB : t (*r medium-label *)
 | t_LTop : t (*r top *)
 | t_VTrue : t (*r Boolean true *)
 | t_VFalse : t (*r Boolean false *)
 | t_VUnit : t (*r unit value *)
 | t_VAbs (x:termvar) (t5:t) (*r abstraction *)
 | t_VLIO (t5:t) (*r LIO value *)
 | t_VLabeled (t1:t) (t2:t) (*r labeled value *)
 | t_VHole : t (*r hole *)
 | t_Var (x:termvar) (*r variable *)
 | t_App (t5:t) (t':t) (*r application *)
 | t_Fix (t5:t) (*r fixpoint *)
 | t_IfEl (t1:t) (t2:t) (t3:t) (*r conditional *)
 | t_Join (t1:t) (t2:t) (*r join *)
 | t_Meet (t1:t) (t2:t) (*r meet *)
 | t_CanFlowTo (t1:t) (t2:t) (*r can-flow-to *)
 | t_Return (t5:t) (*r return *)
 | t_Bind (t5:t) (t':t) (*r bind *)
 | t_GetLabel : t (*r get current label *)
 | t_GetClearance : t (*r get current clearance *)
 | t_LabelOf (t5:t) (*r get label of value *)
 | t_Label (t5:t) (t':t) (*r label *)
 | t_UnLabel (t5:t) (*r unlabel *)
 | t_ToLabeled (t1:t) (t2:t) (*r execute sensitive computation *)
 | t_MkToLabeledTCB (t1:t) (t2:t) (t3:t) (t4:t) (*r trusted primitive that restores state *).

Definition G : Set := list (termvar*T).

Inductive m : Set :=  (*r monadic LIO term *)
 | m_Config (t1:t) (t2:t) (t3:t) (*r configuration *).
Notation G_nil := (@nil (termvar*T)).
Definition bound x T0 G :=
  exists G1, exists G2,
    (G = List.app G1 (List.cons (x,T0) G2)) /\
    ~In x (List.map (@fst termvar T) G1).


(** subrules *)
Definition is_l_of_t (t_6:t) : Prop :=
  match t_6 with
  | t_LBot => (True)
  | t_LA => (True)
  | t_LB => (True)
  | t_LTop => (True)
  | t_VTrue => False
  | t_VFalse => False
  | t_VUnit => False
  | (t_VAbs x t5) => False
  | (t_VLIO t5) => False
  | (t_VLabeled t1 t2) => False
  | t_VHole => False
  | (t_Var x) => False
  | (t_App t5 t') => False
  | (t_Fix t5) => False
  | (t_IfEl t1 t2 t3) => False
  | (t_Join t1 t2) => False
  | (t_Meet t1 t2) => False
  | (t_CanFlowTo t1 t2) => False
  | (t_Return t5) => False
  | (t_Bind t5 t') => False
  | t_GetLabel => False
  | t_GetClearance => False
  | (t_LabelOf t5) => False
  | (t_Label t5 t') => False
  | (t_UnLabel t5) => False
  | (t_ToLabeled t1 t2) => False
  | (t_MkToLabeledTCB t1 t2 t3 t4) => False
end.

Definition is_v_of_t (t_6:t) : Prop :=
  match t_6 with
  | t_LBot => (True)
  | t_LA => (True)
  | t_LB => (True)
  | t_LTop => (True)
  | t_VTrue => (True)
  | t_VFalse => (True)
  | t_VUnit => (True)
  | (t_VAbs x t5) => (True)
  | (t_VLIO t5) => (True)
  | (t_VLabeled t1 t2) => (True)
  | t_VHole => False
  | (t_Var x) => False
  | (t_App t5 t') => False
  | (t_Fix t5) => False
  | (t_IfEl t1 t2 t3) => False
  | (t_Join t1 t2) => False
  | (t_Meet t1 t2) => False
  | (t_CanFlowTo t1 t2) => False
  | (t_Return t5) => False
  | (t_Bind t5 t') => False
  | t_GetLabel => False
  | t_GetClearance => False
  | (t_LabelOf t5) => False
  | (t_Label t5 t') => False
  | (t_UnLabel t5) => False
  | (t_ToLabeled t1 t2) => False
  | (t_MkToLabeledTCB t1 t2 t3 t4) => False
end.


(** free variables *)
Fixpoint fv_t (t_6:t) : list termvar :=
  match t_6 with
  | t_LBot => nil
  | t_LA => nil
  | t_LB => nil
  | t_LTop => nil
  | t_VTrue => nil
  | t_VFalse => nil
  | t_VUnit => nil
  | (t_VAbs x t5) => ((fv_t t5))
  | (t_VLIO t5) => ((fv_t t5))
  | (t_VLabeled t1 t2) => (app (fv_t t1) (fv_t t2))
  | t_VHole => nil
  | (t_Var x) => (cons x nil)
  | (t_App t5 t') => (app (fv_t t5) (fv_t t'))
  | (t_Fix t5) => ((fv_t t5))
  | (t_IfEl t1 t2 t3) => (app (fv_t t1) (app (fv_t t2) (fv_t t3)))
  | (t_Join t1 t2) => (app (fv_t t1) (fv_t t2))
  | (t_Meet t1 t2) => (app (fv_t t1) (fv_t t2))
  | (t_CanFlowTo t1 t2) => (app (fv_t t1) (fv_t t2))
  | (t_Return t5) => ((fv_t t5))
  | (t_Bind t5 t') => (app (fv_t t5) (fv_t t'))
  | t_GetLabel => nil
  | t_GetClearance => nil
  | (t_LabelOf t5) => ((fv_t t5))
  | (t_Label t5 t') => (app (fv_t t5) (fv_t t'))
  | (t_UnLabel t5) => ((fv_t t5))
  | (t_ToLabeled t1 t2) => (app (fv_t t1) (fv_t t2))
  | (t_MkToLabeledTCB t1 t2 t3 t4) => (app (fv_t t1) (app (fv_t t2) (app (fv_t t3) (fv_t t4))))
end.

Definition fv_m (m5:m) : list termvar :=
  match m5 with
  | (m_Config t1 t2 t3) => (app (fv_t t1) (app (fv_t t2) (fv_t t3)))
end.


(** substitutions *)
Fixpoint tsubst_t (t_6:t) (x5:termvar) (t__7:t) {struct t__7} : t :=
  match t__7 with
  | t_LBot => t_LBot 
  | t_LA => t_LA 
  | t_LB => t_LB 
  | t_LTop => t_LTop 
  | t_VTrue => t_VTrue 
  | t_VFalse => t_VFalse 
  | t_VUnit => t_VUnit 
  | (t_VAbs x t5) => t_VAbs x (tsubst_t t_6 x5 t5)
  | (t_VLIO t5) => t_VLIO (tsubst_t t_6 x5 t5)
  | (t_VLabeled t1 t2) => t_VLabeled (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2)
  | t_VHole => t_VHole 
  | (t_Var x) => (if eq_termvar x x5 then t_6 else (t_Var x))
  | (t_App t5 t') => t_App (tsubst_t t_6 x5 t5) (tsubst_t t_6 x5 t')
  | (t_Fix t5) => t_Fix (tsubst_t t_6 x5 t5)
  | (t_IfEl t1 t2 t3) => t_IfEl (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2) (tsubst_t t_6 x5 t3)
  | (t_Join t1 t2) => t_Join (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2)
  | (t_Meet t1 t2) => t_Meet (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2)
  | (t_CanFlowTo t1 t2) => t_CanFlowTo (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2)
  | (t_Return t5) => t_Return (tsubst_t t_6 x5 t5)
  | (t_Bind t5 t') => t_Bind (tsubst_t t_6 x5 t5) (tsubst_t t_6 x5 t')
  | t_GetLabel => t_GetLabel 
  | t_GetClearance => t_GetClearance 
  | (t_LabelOf t5) => t_LabelOf (tsubst_t t_6 x5 t5)
  | (t_Label t5 t') => t_Label (tsubst_t t_6 x5 t5) (tsubst_t t_6 x5 t')
  | (t_UnLabel t5) => t_UnLabel (tsubst_t t_6 x5 t5)
  | (t_ToLabeled t1 t2) => t_ToLabeled (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2)
  | (t_MkToLabeledTCB t1 t2 t3 t4) => t_MkToLabeledTCB (tsubst_t t_6 x5 t1) (tsubst_t t_6 x5 t2) (tsubst_t t_6 x5 t3) (tsubst_t t_6 x5 t4)
end.

Definition tsubst_m (t_5:t) (x5:termvar) (m5:m) : m :=
  match m5 with
  | (m_Config t1 t2 t3) => m_Config (tsubst_t t_5 x5 t1) (tsubst_t t_5 x5 t2) (tsubst_t t_5 x5 t3)
end.

(** definitions *)

(* defns Jtype *)
Inductive GtT : G -> t -> T -> Prop :=    (* defn GtT *)
 | GtT_true : forall (G5:G),
     GtT G5 t_VTrue T_TBool
 | GtT_false : forall (G5:G),
     GtT G5 t_VFalse T_TBool
 | GtT_unit : forall (G5:G),
     GtT G5 t_VUnit T_TUnit
 | GtT_labelBot : forall (G5:G),
     GtT G5 t_LBot T_TLabel
 | GtT_labelA : forall (G5:G),
     GtT G5 t_LA T_TLabel
 | GtT_labelB : forall (G5:G),
     GtT G5 t_LB T_TLabel
 | GtT_labelTop : forall (G5:G),
     GtT G5 t_LTop T_TLabel
 | GtT_labeledVal : forall (G5:G) (t1 t2:t) (T2:T),
     GtT G5 t1 T_TLabel ->
     GtT G5 t2 T2 ->
     GtT G5 (t_VLabeled t1 t2) (T_TLabeled T2)
 | GtT_lioVal : forall (G5:G) (t5:t) (T5:T),
     GtT G5 t5 T5 ->
     GtT G5 (t_VLIO t5) (T_TLIO T5)
 | GtT_hole : forall (G5:G) (T5:T),
     GtT G5 t_VHole T5
 | GtT_valName : forall (G5:G) (x:termvar) (T5:T),
      (bound  x   T5   G5 )  ->
     GtT G5 (t_Var x) T5
 | GtT_abs : forall (G5:G) (x:termvar) (t5:t) (T1 T2:T),
     GtT  (cons ( x , T1 )  G5 )  t5 T2 ->
     GtT G5 (t_VAbs x t5) (T_TArrow T1 T2)
 | GtT_app : forall (G5:G) (t_5 t1:t) (T2 T1:T),
     GtT G5 t_5 (T_TArrow T1 T2) ->
     GtT G5 t1 T1 ->
     GtT G5 (t_App t_5 t1) T2
 | GtT_fix : forall (G5:G) (t5:t) (T5:T),
     GtT G5 t5 (T_TArrow T5 T5) ->
     GtT G5 (t_Fix t5) T5
 | GtT_ifEl : forall (G5:G) (t1 t2 t3:t) (T5:T),
     GtT G5 t1 T_TBool ->
     GtT G5 t2 T5 ->
     GtT G5 t3 T5 ->
     GtT G5 (t_IfEl t1 t2 t3) T5
 | GtT_join : forall (G5:G) (t1 t2:t),
     GtT G5 t2 T_TLabel ->
     GtT G5 (t_Join t1 t2) T_TLabel
 | GtT_meet : forall (G5:G) (t1 t2:t),
     GtT G5 t1 T_TLabel ->
     GtT G5 t2 T_TLabel ->
     GtT G5 (t_Meet t1 t2) T_TLabel
 | GtT_canFlowTo : forall (G5:G) (t1 t2:t),
     GtT G5 t1 T_TLabel ->
     GtT G5 t2 T_TLabel ->
     GtT G5 (t_CanFlowTo t1 t2) T_TBool
 | GtT_return : forall (G5:G) (t5:t) (T5:T),
     GtT G5 t5 T5 ->
     GtT G5 (t_Return t5) (T_TLIO T5)
 | GtT_bind : forall (G5:G) (t5 t':t) (T2 T1:T),
     GtT G5 t5 (T_TLIO T1) ->
     GtT G5 t' (T_TArrow T1 (T_TLIO T2)) ->
     GtT G5 (t_Bind t5 t') (T_TLIO T2)
 | GtT_getLabel : forall (G5:G),
     GtT G5 t_GetLabel (T_TLIO T_TLabel)
 | GtT_getClearance : forall (G5:G),
     GtT G5 t_GetClearance (T_TLIO T_TLabel)
 | GtT_labelOf : forall (G5:G) (t5:t) (T5:T),
     GtT G5 t5 (T_TLabeled T5) ->
     GtT G5 (t_LabelOf t5) T_TLabel
 | GtT_label : forall (G5:G) (t5 t':t) (T5:T),
     GtT G5 t5 T_TLabel ->
     GtT G5 t' T5 ->
     GtT G5 (t_Label t5 t') (T_TLIO  (T_TLabeled T5) )
 | GtT_unlabel : forall (G5:G) (t5:t) (T5:T),
     GtT G5 t5 (T_TLabeled T5) ->
     GtT G5 (t_UnLabel t5) (T_TLIO T5)
 | GtT_toLabeled : forall (G5:G) (t1 t2:t) (T5:T),
     GtT G5 t1 T_TLabel ->
     GtT G5 t2 (T_TLIO T5) ->
     GtT G5 (t_ToLabeled t1 t2) (T_TLIO  (T_TLabeled T5) )
 | GtT_mkToLabeledTCB : forall (G5:G) (t1 t2 t3 t4:t) (T5:T),
     GtT G5 t1 T_TLabel ->
     GtT G5 t2 T_TLabel ->
     GtT G5 t3 T_TLabel ->
     GtT G5 t4 T5 ->
     GtT G5 (t_MkToLabeledTCB t1 t2 t3 t4) (T_TLIO  (T_TLabeled T5) ).
(** definitions *)

(* defns Jpop *)
Inductive pure_reduce : t -> t -> Prop :=    (* defn pure_reduce *)
 | Pr_appCtx : forall (t1 t2 t1':t),
     pure_reduce t1 t1' ->
     pure_reduce (t_App t1 t2) (t_App t1' t2)
 | Pr_app : forall (x:termvar) (t1 t2:t),
     pure_reduce (t_App  (t_VAbs x t1)  t2)  ( tsubst_t  t2   x   t1  ) 
 | Pr_fixCtx : forall (t5 t':t),
     pure_reduce t5 t' ->
     pure_reduce (t_Fix t5) (t_Fix t')
 | Pr_fix : forall (x:termvar) (t5:t),
     pure_reduce (t_Fix  (t_VAbs x t5) )  ( tsubst_t   (t_Fix  (t_VAbs x t5) )    x   t5  ) 
 | Pr_ifCtx : forall (t1 t2 t3 t1':t),
     pure_reduce t1 t1' ->
     pure_reduce (t_IfEl t1 t2 t3) (t_IfEl t1' t2 t3)
 | Pr_ifTrue : forall (t2 t3:t),
     pure_reduce (t_IfEl t_VTrue t2 t3) t2
 | Pr_ifFalse : forall (t2 t3:t),
     pure_reduce (t_IfEl t_VFalse t2 t3) t3
 | Pr_joinCtxL : forall (t1 t2 t1':t),
     pure_reduce t1 t1' ->
     pure_reduce (t_Join t1 t2) (t_Join t1' t2)
 | Pr_joinCtxR : forall (l1 t2 t2':t),
     is_l_of_t l1 ->
     pure_reduce t2 t2' ->
     pure_reduce (t_Join l1 t2) (t_Join l1 t2')
 | Pr_joinBotL : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LBot  ))  ->
     pure_reduce (t_Join t_LBot l5) l5
 | Pr_joinBotR : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LBot  ))  ->
     pure_reduce (t_Join l5 t_LBot) l5
 | Pr_joinEq : forall (l1 l2:t),
     is_l_of_t l1 ->
     is_l_of_t l2 ->
      l1 = l2  ->
     pure_reduce (t_Join l1 l2) l1
 | Pr_joinAB : 
     pure_reduce (t_Join t_LA t_LB) t_LTop
 | Pr_joinBA : 
     pure_reduce (t_Join t_LB t_LA) t_LTop
 | Pr_joinTopL : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LTop  ))  ->
     pure_reduce (t_Join t_LTop l5) t_LTop
 | Pr_joinTopR : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LTop  ))  ->
     pure_reduce (t_Join l5 t_LTop) t_LTop
 | Pr_meetCtxL : forall (t1 t2 t1':t),
     pure_reduce t1 t1' ->
     pure_reduce (t_Meet t1 t2) (t_Meet t1' t2)
 | Pr_meetCtxR : forall (l1 t2 t2':t),
     is_l_of_t l1 ->
     pure_reduce t2 t2' ->
     pure_reduce (t_Meet l1 t2) (t_Meet l1 t2')
 | Pr_meetBotL : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LBot  ))  ->
     pure_reduce (t_Meet t_LBot l5) t_LBot
 | Pr_meetBotR : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LBot  ))  ->
     pure_reduce (t_Meet l5 t_LBot) t_LBot
 | Pr_meetEq : forall (l1 l2:t),
     is_l_of_t l1 ->
     is_l_of_t l2 ->
      l1 = l2  ->
     pure_reduce (t_Meet l1 l2) l1
 | Pr_meetAB : 
     pure_reduce (t_Meet t_LA t_LB) t_LBot
 | Pr_meetBA : 
     pure_reduce (t_Meet t_LB t_LA) t_LBot
 | Pr_meetTopL : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LTop  ))  ->
     pure_reduce (t_Meet t_LTop l5) l5
 | Pr_meetTopR : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LTop  ))  ->
     pure_reduce (t_Meet l5 t_LTop) l5
 | Pr_canFlowToCtxL : forall (t1 t2 t1':t),
     pure_reduce t1 t1' ->
     pure_reduce (t_CanFlowTo t1 t2) (t_CanFlowTo t1' t2)
 | Pr_canFlowToCtxR : forall (l1 t2 t2':t),
     is_l_of_t l1 ->
     pure_reduce t2 t2' ->
     pure_reduce (t_CanFlowTo l1 t2) (t_CanFlowTo l1 t2')
 | Pr_canFlowToBot : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LBot  ))  ->
     pure_reduce (t_CanFlowTo t_LBot l5) t_VTrue
 | Pr_canFlowToEq : forall (l1 l2:t),
     is_l_of_t l1 ->
     is_l_of_t l2 ->
      l1 = l2  ->
     pure_reduce (t_CanFlowTo l1 l2) t_VTrue
 | Pr_canFlowToAB : 
     pure_reduce (t_CanFlowTo t_LA t_LB) t_VFalse
 | Pr_canFlowToBA : 
     pure_reduce (t_CanFlowTo t_LB t_LA) t_VFalse
 | Pr_canFlowToTop : forall (l5:t),
     is_l_of_t l5 ->
      (not (  l5 = t_LTop  ))  ->
     pure_reduce (t_CanFlowTo l5 t_LTop) t_VTrue
 | Pr_labelOfCtx : forall (t5 t':t),
     pure_reduce t5 t' ->
     pure_reduce (t_LabelOf t5) (t_LabelOf t')
 | Pr_labelOf : forall (l1 t2:t),
     is_l_of_t l1 ->
     pure_reduce (t_LabelOf  (t_VLabeled l1 t2) ) l1
 | Pr_hole : 
     pure_reduce t_VHole t_VHole.
(** definitions *)

(* defns Jop *)
Inductive lio_reduce : m -> m -> Prop :=    (* defn lio_reduce *)
 | LIO_return : forall (l5 c t5:t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     lio_reduce (m_Config l5 c (t_Return t5)) (m_Config l5 c (t_VLIO t5))
 | LIO_bindCtx : forall (l5 c t1 t2 l' c' t1':t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     is_l_of_t l' ->
     is_l_of_t c' ->
     lio_reduce (m_Config l5 c t1) (m_Config l' c' t1') ->
     lio_reduce (m_Config l5 c (t_Bind t1 t2)) (m_Config l' c' (t_Bind t1' t2))
 | LIO_bind : forall (l5 c t1 t2:t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     lio_reduce (m_Config l5 c (t_Bind (t_VLIO t1) t2)) (m_Config l5 c  (t_App t2 t1) )
 | LIO_getLabel : forall (l5 c:t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     lio_reduce (m_Config l5 c t_GetLabel) (m_Config l5 c (t_Return l5))
 | LIO_getClearance : forall (l5 c:t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     lio_reduce (m_Config l5 c t_GetClearance) (m_Config l5 c (t_Return c))
 | LIO_labelCtx : forall (l5 c t1 t2 t1':t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     pure_reduce t1 t1' ->
     lio_reduce (m_Config l5 c (t_Label t1 t2)) (m_Config l5 c (t_Label t1' t2))
 | LIO_label : forall (l_5 c l1 t2:t),
     is_l_of_t l_5 ->
     is_l_of_t c ->
     is_l_of_t l1 ->
     pure_reduce (t_CanFlowTo l_5 l1) t_VTrue ->
     pure_reduce (t_CanFlowTo l1 c) t_VTrue ->
     lio_reduce (m_Config l_5 c (t_Label l1 t2)) (m_Config l_5 c (t_Return  (t_VLabeled l1 t2) ))
 | LIO_unlabelCtx : forall (l5 c t5 t':t),
     is_l_of_t l5 ->
     is_l_of_t c ->
     pure_reduce t5 t' ->
     lio_reduce (m_Config l5 c (t_UnLabel t5)) (m_Config l5 c (t_UnLabel t'))
 | LIO_unlabel : forall (l_5 c l1 t2 l2:t),
     is_l_of_t l_5 ->
     is_l_of_t c ->
     is_l_of_t l1 ->
     is_l_of_t l2 ->
     pure_reduce (t_Join l_5 l1) l2 ->
     pure_reduce (t_CanFlowTo l2 c) t_VTrue ->
     lio_reduce (m_Config l_5 c (t_UnLabel  (t_VLabeled l1 t2) )) (m_Config l2 c (t_Return t2))
 | LIO_toLabeled : forall (l_5 c l1 t5:t) (x:termvar),
     is_l_of_t l_5 ->
     is_l_of_t c ->
     is_l_of_t l1 ->
     pure_reduce (t_CanFlowTo l_5 l1) t_VTrue ->
     pure_reduce (t_CanFlowTo l1 c) t_VTrue ->
     lio_reduce (m_Config l_5 c (t_ToLabeled l1 t5)) (m_Config l_5 c (t_Bind t5  (t_VAbs x (t_MkToLabeledTCB l_5 c l1 (t_Var x))) ))
 | LIO_mkToLabeledTCB : forall (l_5 c l' c' l1 t5:t),
     is_l_of_t l_5 ->
     is_l_of_t c ->
     is_l_of_t l' ->
     is_l_of_t c' ->
     is_l_of_t l1 ->
     pure_reduce (t_CanFlowTo l_5 l1) t_VTrue ->
     lio_reduce (m_Config l_5 c (t_MkToLabeledTCB l' c' l1 t5)) (m_Config l' c' (t_Label l1 t5))
 | LIO_hole : 
     lio_reduce (m_Config t_VHole t_VHole t_VHole) (m_Config t_VHole t_VHole t_VHole).
Hint Constructors pure_reduce lio_reduce GtT : rules.

Tactic Notation "label_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "label_LBot"
  | Case_aux c "label_LA"
  | Case_aux c "label_LB"
  | Case_aux c "label_LTop" ].

Tactic Notation "value_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "value_LBot"
  | Case_aux c "value_LA"
  | Case_aux c "value_LB"
  | Case_aux c "value_LTop"
  | Case_aux c "value_VTrue"
  | Case_aux c "value_VFalse"
  | Case_aux c "value_VUnit"
  | Case_aux c "value_VAbs"
  | Case_aux c "value_VLIO"
  | Case_aux c "value_VLabeled" ].

Tactic Notation "term_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "term_LBot"
  | Case_aux c "term_LA"
  | Case_aux c "term_LB"
  | Case_aux c "term_LTop"
  | Case_aux c "term_VTrue"
  | Case_aux c "term_VFalse"
  | Case_aux c "term_VUnit"
  | Case_aux c "term_VAbs"
  | Case_aux c "term_VLIO"
  | Case_aux c "term_VLabeled"
  | Case_aux c "term_VHole"
  | Case_aux c "term_Var"
  | Case_aux c "term_App"
  | Case_aux c "term_Fix"
  | Case_aux c "term_IfEl"
  | Case_aux c "term_Join"
  | Case_aux c "term_Meet"
  | Case_aux c "term_CanFlowTo"
  | Case_aux c "term_Return"
  | Case_aux c "term_Bind"
  | Case_aux c "term_GetLabel"
  | Case_aux c "term_GetClearance"
  | Case_aux c "term_LabelOf"
  | Case_aux c "term_Label"
  | Case_aux c "term_UnLabel"
  | Case_aux c "term_ToLabeled"
  | Case_aux c "term_MkToLabeledTCB" ].

Tactic Notation "type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "GtT_true"
  | Case_aux c "GtT_false"
  | Case_aux c "GtT_unit"
  | Case_aux c "GtT_labelBot"
  | Case_aux c "GtT_labelA"
  | Case_aux c "GtT_labelB"
  | Case_aux c "GtT_labelTop"
  | Case_aux c "GtT_labeledVal"
  | Case_aux c "GtT_lioVal"
  | Case_aux c "GtT_hole"
  | Case_aux c "GtT_valName"
  | Case_aux c "GtT_abs"
  | Case_aux c "GtT_fix"
  | Case_aux c "GtT_app"
  | Case_aux c "GtT_ifEl"
  | Case_aux c "GtT_join"
  | Case_aux c "GtT_meet"
  | Case_aux c "GtT_canFlowTo"
  | Case_aux c "GtT_return"
  | Case_aux c "GtT_bind"
  | Case_aux c "GtT_getLabel"
  | Case_aux c "GtT_getClearance"
  | Case_aux c "GtT_labelOf"
  | Case_aux c "GtT_label"
  | Case_aux c "GtT_unlabel" ].

Tactic Notation "pure_reduce_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Pr_appCtx"
  | Case_aux c "Pr_app"
  | Case_aux c "Pr_fixCtx"
  | Case_aux c "Pr_fix"
  | Case_aux c "Pr_ifCtx"
  | Case_aux c "Pr_ifTrue"
  | Case_aux c "Pr_ifFalse"
  | Case_aux c "Pr_joinCtxL"
  | Case_aux c "Pr_joinCtxR"
  | Case_aux c "Pr_joinBotL"
  | Case_aux c "Pr_joinBotR"
  | Case_aux c "Pr_joinEq"
  | Case_aux c "Pr_joinAB"
  | Case_aux c "Pr_joinBA"
  | Case_aux c "Pr_joinTopL"
  | Case_aux c "Pr_joinTopR"
  | Case_aux c "Pr_meetCtxL"
  | Case_aux c "Pr_meetCtxR"
  | Case_aux c "Pr_meetBotL"
  | Case_aux c "Pr_meetBotR"
  | Case_aux c "Pr_meetEq"
  | Case_aux c "Pr_meetAB"
  | Case_aux c "Pr_meetBA"
  | Case_aux c "Pr_meetTopL"
  | Case_aux c "Pr_meetTopR"
  | Case_aux c "Pr_canFlowToCtxL"
  | Case_aux c "Pr_canFlowToCtxR"
  | Case_aux c "Pr_canFlowToBot"
  | Case_aux c "Pr_canFlowToEq"
  | Case_aux c "Pr_canFlowToAB"
  | Case_aux c "Pr_canFlowToBA"
  | Case_aux c "Pr_canFlowToTop"
  | Case_aux c "Pr_labelOfCtx"
  | Case_aux c "Pr_labelOf"
  | Case_aux c "Pr_hole" ].


Tactic Notation "lio_reduce_cases" tactic(first) ident(c) :=
 first;
  [ Case_aux c "LIO_return"
  | Case_aux c "LIO_bindCtx"
  | Case_aux c "LIO_bind"
  | Case_aux c "LIO_getLabel"
  | Case_aux c "LIO_getClearance"
  | Case_aux c "LIO_labelCtx"
  | Case_aux c "LIO_label"
  | Case_aux c "LIO_unlabelCtx"
  | Case_aux c "LIO_unlabel"
  | Case_aux c "LIO_toLabeled"
  | Case_aux c "LIO_mkToLabeledTCB"
  | Case_aux c "LIO_hole" ].




