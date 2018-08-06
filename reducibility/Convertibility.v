Require Import Setoid Morphisms Term.

Inductive reduction : term -> term -> Prop :=
| reduction_β : forall t u, reduction (app (lam t) u) (subs_term (CONS u ESID) t)
| reduction_η : forall t, reduction (lam (app (lift_term (ELSHFT ELID) t) (var 0))) t
| reduction_ι_l : forall t u1 u2, reduction (cse (lft t) u1 u2) (subs_term (CONS t ESID) u1)
| reduction_ι_r : forall t u1 u2, reduction (cse (rgt t) u1 u2) (subs_term (CONS t ESID) u2)
| reduction_lam : forall t r, reduction t r -> reduction (lam t) (lam r)
| reduction_app_l : forall t u r, reduction t r -> reduction (app t u) (app r u)
| reduction_app_r : forall t u r, reduction u r -> reduction (app t u) (app t r)
| reduction_lft : forall t r, reduction t r -> reduction (lft t) (lft r)
| reduction_rgt : forall t r, reduction t r -> reduction (rgt t) (rgt r)
| reduction_cse_e : forall t u1 u2 r, reduction t r -> reduction (cse t u1 u2) (cse r u1 u2)
| reduction_cse_l : forall t u1 u2 r, reduction u1 r -> reduction (cse t u1 u2) (cse t r u2)
| reduction_cse_r : forall t u1 u2 r, reduction u2 r -> reduction (cse t u1 u2) (cse t u1 r)
.

Inductive convertible : term -> term -> Prop :=
| convertible_refl : forall t, convertible t t
| convertible_sym : forall t u, convertible t u -> convertible u t
| convertible_trans : forall t u r, convertible t u -> convertible u r -> convertible t r
| convertible_step : forall t u, reduction t u -> convertible t u.

Instance Equivalence_convertible : RelationClasses.Equivalence convertible.
Proof.
split.
+ intro; apply convertible_refl.
+ intros x y; apply convertible_sym.
+ intros x y z; apply convertible_trans.
Qed.

Definition convertible_β t u := convertible_step _ _ (reduction_β t u).
Definition convertible_η t := convertible_step _ _ (reduction_η t).

Lemma convertible_app_l : forall t u r,
  convertible t r -> convertible (app t u) (app r u).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (app u0 u); assumption.
+ apply convertible_step, reduction_app_l; assumption.
Qed.

Lemma convertible_app_r : forall t u r,
  convertible u r -> convertible (app t u) (app t r).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (app t u); assumption.
+ apply convertible_step, reduction_app_r; assumption.
Qed.

Lemma convertible_lam : forall t r,
  convertible t r -> convertible (lam t) (lam r).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (lam u); assumption.
+ apply convertible_step, reduction_lam; assumption.
Qed.

Instance Proper_convertible_app : Proper (convertible ==> convertible ==> convertible) app.
Proof.
intros t1 t2 Ht u1 u2 Hu.
transitivity (app t1 u2).
+ apply convertible_app_r; assumption.
+ apply convertible_app_l; assumption.
Qed.

Lemma convertible_lft : forall t r,
  convertible t r -> convertible (lft t) (lft r).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (lft u); assumption.
+ apply convertible_step, reduction_lft; assumption.
Qed.

Lemma convertible_rgt : forall t r,
  convertible t r -> convertible (rgt t) (rgt r).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (rgt u); assumption.
+ apply convertible_step, reduction_rgt; assumption.
Qed.

Lemma convertible_cse_e : forall t u1 u2 r,
  convertible t r -> convertible (cse t u1 u2) (cse r u1 u2).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (cse u u1 u2); assumption.
+ apply convertible_step, reduction_cse_e; assumption.
Qed.

Lemma convertible_cse_l : forall t u1 u2 r,
  convertible u1 r -> convertible (cse t u1 u2) (cse t r u2).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (cse t u u2); assumption.
+ apply convertible_step, reduction_cse_l; assumption.
Qed.

Lemma convertible_cse_r : forall t u1 u2 r,
  convertible u2 r -> convertible (cse t u1 u2) (cse t u1 r).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ transitivity (cse t u1 u); assumption.
+ apply convertible_step, reduction_cse_r; assumption.
Qed.

Lemma convertible_cse : forall t u1 u2 r r1 r2,
  convertible t r ->
  convertible u1 r1 ->
  convertible u2 r2 ->
  convertible (cse t u1 u2) (cse r r1 r2).
Proof.
intros t u1 u2 r r1 r2 H H1 H2.
etransitivity; [apply convertible_cse_e; eassumption|].
etransitivity; [apply convertible_cse_l; eassumption|].
etransitivity; [apply convertible_cse_r; eassumption|].
reflexivity.
Qed.

Lemma subs_term_CONS_LFT_n : forall t u e n,
subs_term (LIFTn n (CONS (lift_term e u) ESID)) (lift_term (ELLFTn n (ELLFT e)) t) =
lift_term (ELLFTn n e) (subs_term (LIFTn n (CONS u ESID)) t).
Proof.
induction t; intros u e m; cbn.
+ revert n u e; induction m as [|m]; intros n u e; cbn.
  - rewrite !expand_term_CONS; destruct n as [|n]; reflexivity.
  - rewrite !expand_term_LIFT; destruct n as [|n]; [reflexivity|].
    rewrite IHm, <- !lift_term_compose; f_equal; cbn; f_equal.
    rewrite lift_compose_ELID_r; reflexivity.
+ f_equal; intuition.
+ f_equal; apply (IHt _ _ (S m)).
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - apply (IHt2 _ _ (S m)).
  - apply (IHt3 _ _ (S m)).
Qed.

Lemma subs_term_LFT_CONS : forall t u e,
  subs_term (CONS (lift_term e u) ESID) (lift_term (ELLFT e) t) =
  lift_term e (subs_term (CONS u ESID) t).
Proof.
induction t; intros u e; cbn.
- rewrite !expand_term_CONS; destruct n as [|n]; reflexivity.
- f_equal; intuition.
- f_equal.
  apply subs_term_CONS_LFT_n with (n := 1).
- f_equal; intuition.
- f_equal; intuition.
- f_equal; intuition; apply subs_term_CONS_LFT_n with (n := 1).
Qed.

Lemma reduction_lift : forall t r e,
  reduction t r -> reduction (lift_term e t) (lift_term e r).
Proof.
intros t r e Hr; revert e; induction Hr; intros e; cbn in *.
+ evar (r : term); match goal with [ |- reduction _ ?t ] => replace t with r; [refine (reduction_β _ _)|] end;
  unfold r; clear r.
  apply subs_term_LFT_CONS.
+ rewrite <- lift_term_compose; cbn.
  rewrite lift_compose_ELID_r.
  replace (lift_term (ELSHFT e) t) with (lift_term (ELSHFT ELID) (lift_term e t)).
  - apply reduction_η.
  - rewrite <- lift_term_compose; reflexivity.
+ evar (r : term); match goal with [ |- reduction _ ?t ] => replace t with r; [refine (reduction_ι_l _ _ _)|] end;
  unfold r; clear r.
  apply subs_term_LFT_CONS.
+ evar (r : term); match goal with [ |- reduction _ ?t ] => replace t with r; [refine (reduction_ι_r _ _ _)|] end;
  unfold r; clear r.
  apply subs_term_LFT_CONS.
+ apply reduction_lam; intuition.
+ apply reduction_app_l; intuition.
+ apply reduction_app_r; intuition.
+ apply reduction_lft; intuition.
+ apply reduction_rgt; intuition.
+ apply reduction_cse_e; intuition.
+ apply reduction_cse_l; intuition.
+ apply reduction_cse_r; intuition.
Qed.

Lemma convertible_lift : forall t r e,
  convertible t r -> convertible (lift_term e t) (lift_term e r).
Proof.
induction 1.
+ reflexivity.
+ symmetry; assumption.
+ etransitivity; eassumption.
+ apply convertible_step, reduction_lift; assumption.
Qed.
