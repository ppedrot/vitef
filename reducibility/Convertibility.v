Require Import Setoid CMorphisms Term.

Inductive reduction : term -> term -> Type :=
| reduction_β : forall t u, reduction (app (lam t) u) (subs_term (CONS u ESID) t)
| reduction_η : forall t, reduction (lam (app (lift_term (ELSHFT ELID) t) (var 0))) t
| reduction_lam : forall t r, reduction t r -> reduction (lam t) (lam r)
| reduction_app_l : forall t u r, reduction t r -> reduction (app t u) (app r u)
| reduction_app_r : forall t u r, reduction u r -> reduction (app t u) (app t r)
.

Inductive convertible : term -> term -> Type :=
| convertible_refl : forall t, convertible t t
| convertible_sym : forall t u, convertible t u -> convertible u t
| convertible_trans : forall t u r, convertible t u -> convertible u r -> convertible t r
| convertible_step : forall t u, reduction t u -> convertible t u.

Instance Equivalence_convertible : CRelationClasses.Equivalence convertible.
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
Qed.

Lemma reduction_lift : forall t r e,
  reduction t r -> reduction (lift_term e t) (lift_term e r).
Proof.
intros t r e Hr; revert e; induction Hr; intros e; cbn in *.
+ evar (r : term); match goal with [ |- reduction _ ?t ] => replace t with r; [refine (reduction_β _ _)|] end;
  unfold r; clear r.
  revert u e; induction t; intros u e; cbn.
  - rewrite !expand_term_CONS; destruct n as [|n]; reflexivity.
  - f_equal; intuition.
  - f_equal.
    apply subs_term_CONS_LFT_n with (n := 1).
+ rewrite <- lift_term_compose; cbn.
  rewrite lift_compose_ELID_r.
  replace (lift_term (ELSHFT e) t) with (lift_term (ELSHFT ELID) (lift_term e t)).
  - apply reduction_η.
  - rewrite <- lift_term_compose; reflexivity.
+ apply reduction_lam; intuition.
+ apply reduction_app_l; intuition.
+ apply reduction_app_r; intuition.
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
