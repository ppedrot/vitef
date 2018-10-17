Require List.
Require Import CMorphisms PeanoNat Omega.

Require Import Term Convertibility Typing.

Set Primitive Projections.
Set Implicit Arguments.

Record eval_ntr (Γ : list type) A (t : term) := {
  eval_atm_red : term;
  eval_atm_typ : inhabited [ Γ ⊢ne eval_atm_red : A ];
  eval_atm_cnv : convertible t eval_atm_red;
}.

Definition eval_atm Γ n t := eval_ntr Γ (atm n) t.

Inductive eval_sum evalA evalB Γ A B t :=
| eval_sum_lft :
  forall r, (forall Δ e (eε : typing_lift e Δ Γ), evalA Δ (lift_term e r)) -> convertible t (lft r) -> eval_sum evalA evalB Γ A B t
| eval_sum_rgt :
  forall r, (forall Δ e (eε : typing_lift e Δ Γ), evalB Δ (lift_term e r)) -> convertible t (rgt r) -> eval_sum evalA evalB Γ A B t
| eval_sum_ntr : eval_ntr Γ (sum A B) t -> eval_sum evalA evalB Γ A B t
.

Unset Implicit Arguments.

Fixpoint eval (Γ : list type) (A : type) (t : term) {struct A} : Type :=
match A with
| atm n => eval_atm Γ n t
| arr A B =>
  forall (x : term)
  (xε : forall Δ (e : lift) (eε : typing_lift e Δ Γ), eval Δ A (lift_term e x)), eval Γ B (app t x)
| sum A B => eval_sum (fun Γ => eval Γ A) (fun Γ => eval Γ B) Γ A B t
end.

Definition realizes Γ A t :=
  (forall Δ e (eε : typing_lift e Δ Γ), eval Δ A (lift_term e t)).

(*
Lemma lift_eval_ntr : forall Γ Δ A t e, [ Δ ⊢lift e : Γ ] ->
  eval_ntr Γ A t -> eval_ntr Δ A (lift_term e t).
Proof.
intros Γ Δ A t e He Ht.
destruct Ht as [r Htr Hr]; exists (lift_term e r).
- destruct Htr as [Htr]; constructor; apply NF_typing_lift_compat with Γ; assumption.
- apply convertible_lift; assumption.
Qed.

Lemma lift_eval : forall Γ Δ A t e, [ Δ ⊢lift e : Γ ] ->
  eval Γ A t -> eval Δ A (lift_term e t).
Proof.
intros Γ Δ A; revert Γ Δ; induction A; intros Γ Δ t e He Ht; cbn in *.
+ eapply lift_eval_ntr; eassumption.
+ intros Ξ e' He' x xε.
  rewrite <- lift_term_compose.
  apply Ht; [|assumption].
  apply typing_lift_compose with Δ; assumption.
+ destruct Ht as [r Htr Hr|r Htr Hr|Ht].
  - apply eval_sum_lft with (lift_term e r).
    { apply IHA1 with Γ; assumption. }
    { apply convertible_lift with (r := lft _); assumption. }
  - apply eval_sum_rgt with (lift_term e r).
    { apply IHA2 with Γ; assumption. }
    { apply convertible_lift with (r := rgt _); assumption. }
  - apply eval_sum_ntr; eapply lift_eval_ntr; eassumption.
Qed.
*)
(* Definition realizes Γ A t := forall Δ (e : lift) (eε : typing_lift e Δ Γ), eval Δ A (lift_term e t). *)

Lemma eval_ntr_convertible_compat : forall Γ A t r, convertible t r -> eval_ntr Γ A t -> eval_ntr Γ A r.
Proof.
intros Γ A t r Hr Ht.
destruct Ht as [s Hs H]; exists s.
- assumption.
- apply convertible_trans with t; [|assumption].
  apply convertible_sym; assumption.
Qed.

Lemma eval_convertible_compat : forall Γ A t r, convertible t r -> eval Γ A t -> eval Γ A r.
Proof.
intros Γ A; revert Γ; induction A as [n|A IHA B IHB|A IHA B IHB]; intros Γ t r Hr Ht; cbn in *.
+ eapply eval_ntr_convertible_compat; eassumption.
+ intros x xε.
  apply IHB with (app t x).
  rewrite Hr; reflexivity.
  apply Ht, xε.
+ destruct Ht as [x xε Hx|y yε Hy|n].
  - apply (eval_sum_lft _ _ _ _ xε).
    rewrite <- Hx; symmetry; assumption.
  - apply (eval_sum_rgt _ _ _ _ yε).
    rewrite <- Hy; symmetry; assumption.
  - eapply eval_sum_ntr, eval_ntr_convertible_compat; eassumption.
Qed.

Instance Proper_eval : Proper (eq ==> eq ==> convertible ==> iffT) eval.
Proof.
intros Γ Γ' <- A A' <- t t' Ht; split; intros; eapply eval_convertible_compat; try eassumption.
symmetry; eassumption.
Qed.

Inductive eval_subs : list type -> list type -> subs term -> Type :=
| eval_subs_ESID : forall Γ e, eval_subs Γ nil (subs_of_lift e)
| eval_subs_CONS : forall Γ Δ A t σ, realizes Γ A t -> eval_subs Γ Δ σ -> eval_subs Γ (cons A Δ) (CONS t σ)
| eval_subs_SHFT : forall Γ Δ A σ, eval_subs Γ Δ σ -> eval_subs (cons A Γ) Δ (SHFT σ)
(* | eval_subs_LIFT : forall Γ Δ A σ, eval_subs Γ Δ σ -> eval_subs (cons A Γ) (cons A Δ) (LIFT σ) *)
.

Set Implicit Arguments.

Record reified Γ A t := Reified {
  reify_trm : term;
  reify_typ : inhabited [ Γ ⊢nf reify_trm : A ];
  reify_cvn : convertible t reify_trm;
}.

Record interp (A : type) := {
  reflect : forall Γ t, inhabited [ Γ ⊢ne t : A ] -> realizes Γ A t;
  reify : forall Γ t, realizes Γ A t -> reified Γ A t;
}.

Unset Implicit Arguments.

Lemma completeness : forall A, interp A.
Proof.
induction A; split; cbn in *.
+ intros Γ t Ht Δ e eε; cbn in *.
  exists (lift_term e t); [|constructor].
  destruct Ht; constructor.
  eapply NF_typing_lift_compat; eassumption.
+ intros Γ t Ht.
  specialize (Ht Γ ELID (typing_ELID _)).
  rewrite lift_term_ELID in Ht.
  unshelve refine (Reified _ _).
  - cbn in *.
    refine (Ht.(eval_atm_red)).
  - destruct Ht as [? [Ht] ?]; cbn in *.
    constructor. apply NF.typing_ne; apply Ht.
  - cbn in *.
    destruct Ht as [r ? Hr]; cbn.
    assumption.
+ intros Γ t Ht Δ e eε; cbn in *; intros x xε.
  destruct (@reify A1 IHA1 Δ x xε) as [r Hr Hrx].
  apply eval_convertible_compat with (app (lift_term e t) r).
  { rewrite Hrx; reflexivity. }
  rewrite <- (lift_term_ELID (app (lift_term e t) r)).
  refine (IHA2.(reflect) _ (typing_ELID _)).
  destruct Hr as [Hr], Ht as [Ht]; constructor.
  apply NF.typing_app with A1; [|assumption].
  apply NF_typing_lift_compat with Γ; assumption.
+ intros Γ t Ht.
  assert (xε : realizes (A1 :: Γ) A2 (app (lift_term (ELSHFT ELID) t) (var 0))).
  { intros Δ e eε; specialize (Ht Δ).
    cbn in *.
    fold (lift_term e (var 0)).
    rewrite <- lift_term_compose.
    refine (Ht _ _ _ _); [eapply typing_lift_compose; [eassumption|repeat constructor]|].
    intros Ξ e' eε'.
    rewrite <- lift_term_compose.
    refine (@reflect _ IHA1 (cons A1 Γ) _ _ _ _ _).
    { repeat constructor. }
    { eapply typing_lift_compose; eassumption. }
  }
  assert (r := @reify _ IHA2 (cons A1 Γ) (app (lift_term (ELSHFT ELID) t) (var 0)) xε).
  destruct r as [r Hr Hre].
  unshelve refine (Reified _ _).
  - refine (lam r).
  - destruct Hr as [Hr]; constructor; cbn.
    apply NF.typing_lam; assumption.
  - rewrite <- Hre, convertible_η; reflexivity.
+ intros Γ t Ht Δ e eε.
  apply eval_sum_ntr; exists (lift_term e t).
  - destruct Ht as [Ht]; constructor.
    eapply NF_typing_lift_compat; eassumption.
  - reflexivity.
+ intros Γ t Ht.
  destruct Ht as [r Htr Hr|r Htr Hr|[r Htr Hr]].
  - unshelve refine (Reified _ _); cbn.
    { exact (lft ((IHA1.(reify) _ _ Htr).(reify_trm))). }
    { destruct (IHA1.(reify)) as [s [Hts] Hs].
     cbn; constructor; apply NF.typing_lft; assumption. }
    { rewrite Hr; apply convertible_lft, IHA1.(reify). }
  - unshelve refine (Reified _ _); cbn.
    { exact (rgt ((IHA2.(reify) _ _ Htr).(reify_trm))). }
    { destruct (IHA2.(reify)) as [s [Hts] Hs].
     cbn; constructor; apply NF.typing_rgt; assumption. }
    { rewrite Hr; apply convertible_rgt, IHA2.(reify). }
  - unshelve refine (Reified _ _); cbn.
    { refine r. }
    { destruct Htr as [Htr]; constructor; apply NF.typing_ne; assumption. }
    { assumption. }
Qed.

Lemma subs_term_CONS_SHFT_LIFT_n : forall t σ n,
  subs_term (LIFTn n (CONS (var 0) (SHFT σ))) t = subs_term (LIFTn (S n) σ) t.
Proof.
induction t; intros σ m; cbn in *; try (solve [f_equal; intuition eauto]).
+ revert n σ; induction m as [|m]; intros n σ; cbn.
  - rewrite expand_term_CONS, expand_term_LIFT.
    destruct n as [|n]; [reflexivity|].
    rewrite expand_term_SHFT; f_equal.
  - rewrite !expand_term_LIFT; destruct n as [|n]; [reflexivity|]; cbn.
    f_equal; apply IHm.
+ f_equal; apply (IHt _ (S m)).
+ f_equal; [intuition|apply (IHt2 _ (S m))|apply (IHt3 _ (S m))].
Qed.

Lemma subs_term_CONS_SHFT_LIFT : forall t σ,
  subs_term (CONS (var 0) (SHFT σ)) t = subs_term (LIFT σ) t.
Proof.
intros t σ; apply subs_term_CONS_SHFT_LIFT_n with (n := 0).
Qed.

(* Γ ⊢ t : A -> α ⊩ Γ -> α ⊩ A *)
Lemma soundness : forall Γ Δ A t σ,
  [ Γ ⊢ t : A ] -> eval_subs Δ Γ σ -> eval Δ A (subs_term σ t).
Proof.
intros Γ Δ A t σ Ht; revert Δ σ; induction Ht; cbn in *; intros Δ σ Hσ.
+ revert n A e; induction Hσ; intros n B e'; cbn in *.
  - apply List.nth_error_In in e'; elim e'.
  - destruct n as [|n]; cbn in *.
    { injection e'; intros ->; rewrite lift_term_ELID; apply e; constructor. }
    { apply IHHσ; assumption. }
  - rewrite expand_term_SHFT.
    apply lift_eval with Γ; [repeat constructor|].
    apply IHHσ; assumption.
+ intros Ξ e eε x xε.
  eapply eval_convertible_compat; [symmetry; apply convertible_β|].
  rewrite <- subs_term_lift, <- !subs_term_compose; cbn.
  apply IHHt. constructor; [assumption|].
  clear - eε Hσ.
  revert Γ σ Hσ; induction eε; intros Ξ σ Hσ; cbn.
  - assumption.
  - constructor; apply IHeε; assumption.
  - remember (A :: Δ)%list as Ω; revert A Δ eε IHeε HeqΩ; induction Hσ; intros B Ξ eε IHeε HeqΩ; subst.
    { clear. destruct e; cbn.
      - change (LIFT (subs_of_lift el)) with (@subs_of_lift term (ELLFT el)); constructor.
      - rewrite <- subs_lift_compose; do 2 constructor.
      - rewrite <- subs_lift_compose. refine (eval_subs_ESID _ (ELLFT _)).
    }
    { constructor.
      + change (LIFT (subs_of_lift el)) with (@subs_of_lift term (ELLFT el)).
        rewrite subs_term_lift; eapply lift_eval; [constructor|]; eassumption.
      + eapply IHHσ; [eassumption|eassumption|reflexivity]. }
    { constructor; apply IHeε.
      injection HeqΩ; intros -> ->; assumption. }
+ rewrite <- (lift_term_ELID (subs_term σ t)).
  apply IHHt1 with Δ.
  - assumption.
  - constructor.
  - apply IHHt2; assumption.
+ apply eval_sum_lft with (subs_term σ t).
  - apply IHHt; assumption.
  - reflexivity.
+ apply eval_sum_rgt with (subs_term σ t).
  - apply IHHt; assumption.
  - reflexivity.
+ destruct (IHHt1 _ _ Hσ) as [r Htr Hr|r Htr Hr|[r Htr Hr]].
  - eapply eval_convertible_compat.
    { apply convertible_cse_e; symmetry; eassumption. }
    eapply eval_convertible_compat; [symmetry; eapply convertible_step, reduction_ι_l|].
    rewrite <- subs_term_compose; cbn.
    apply IHHt2; constructor; assumption.
  - eapply eval_convertible_compat.
    { apply convertible_cse_e; symmetry; eassumption. }
    eapply eval_convertible_compat; [symmetry; eapply convertible_step, reduction_ι_r|].
    rewrite <- subs_term_compose; cbn.
    apply IHHt3; constructor; assumption.
  - unshelve refine (let r1 := (completeness C).(reify) _ _ (IHHt2 (cons A Δ) (CONS (var 0) (SHFT σ)) _) in _).
    { apply eval_subs_CONS, eval_subs_SHFT, Hσ.
      apply (completeness A).
      constructor; apply (NF.typing_var _ _ 0); reflexivity. }
    unshelve refine (let r2 := (completeness C).(reify) _ _ (IHHt3 (cons B Δ) (CONS (var 0) (SHFT σ)) _) in _).
    { apply eval_subs_CONS, eval_subs_SHFT, Hσ.
      apply (completeness B).
      constructor; apply (NF.typing_var _ _ 0); reflexivity. }
    apply eval_convertible_compat with (cse r r1.(reify_trm) r2.(reify_trm)).
    { apply convertible_cse.
      + symmetry; apply Hr.
      + rewrite <- r1.(reify_cvn).
        rewrite subs_term_CONS_SHFT_LIFT; reflexivity.
      + rewrite <- r2.(reify_cvn).
        rewrite subs_term_CONS_SHFT_LIFT; reflexivity.
    }
    apply (completeness C).(reflect).
    destruct Htr as [Htr], r1.(reify_typ) as [rt1], r2.(reify_typ) as [rt2].
    constructor; apply NF.typing_cse with A B; assumption.
Qed.
