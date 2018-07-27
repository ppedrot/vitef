Require List.
Require Import CMorphisms PeanoNat Omega.

Require Import Term Convertibility Typing.

Set Primitive Projections.
Set Implicit Arguments.

Record eval_atm (Γ : list type) n (t : term) := {
  eval_atm_red : term;
  eval_atm_typ : [ Γ ⊢ne eval_atm_red : atm n ];
  eval_atm_cnv : convertible t eval_atm_red;
}.

Unset Implicit Arguments.

Fixpoint eval (Γ : list type) (A : type) (t : term) : Type :=
match A with
| atm n => eval_atm Γ n t
| arr A B =>
  forall Δ (e : lift) (eε : typing_lift e Δ Γ),
  forall (x : term) (xε : eval Δ A x), eval Δ B (app (lift_term e t) x)
end.

Notation realizes := eval.

Lemma lift_eval : forall Γ Δ A t e, [ Δ ⊢lift e : Γ ] ->
  eval Γ A t -> eval Δ A (lift_term e t).
Proof.
intros Γ Δ A; revert Γ Δ; induction A; intros Γ Δ t e He Ht; cbn in *.
+ destruct Ht as [r Htr Hr]; exists (lift_term e r).
  - apply NF_typing_lift_compat with Γ; assumption.
  - apply convertible_lift; assumption.
+ intros Ξ e' He' x xε.
  rewrite <- lift_term_compose.
  apply Ht; [|assumption].
  apply typing_lift_compose with Δ; assumption.
Qed.

(* Definition realizes Γ A t := forall Δ (e : lift) (eε : typing_lift e Δ Γ), eval Δ A (lift_term e t). *)

Lemma eval_convertible_compat : forall Γ A t r, convertible t r -> eval Γ A t -> eval Γ A r.
Proof.
intros Γ A; revert Γ; induction A as [n|A IHA B IHB]; intros Γ t r Hr Ht; cbn in *.
+ destruct Ht as [s Hs H]; exists s.
  - assumption.
  - apply convertible_trans with t; [|assumption].
    apply convertible_sym; assumption.
+ intros Δ e He x xε.
  apply IHB with (app (lift_term e t) x).
  - apply convertible_app_l, convertible_lift; assumption.
  - apply Ht, xε; assumption.
Qed.

Inductive eval_subs : list type -> list type -> subs term -> Type :=
| eval_subs_ESID : forall Γ e, eval_subs Γ nil (subs_of_lift e)
| eval_subs_CONS : forall Γ Δ A t σ, realizes Γ A t -> eval_subs Γ Δ σ -> eval_subs Γ (cons A Δ) (CONS t σ)
| eval_subs_SHFT : forall Γ Δ A σ, eval_subs Γ Δ σ -> eval_subs (cons A Γ) Δ (SHFT σ)
(* | eval_subs_LIFT : forall Γ Δ A σ, eval_subs Γ Δ σ -> eval_subs (cons A Γ) (cons A Δ) (LIFT σ) *)
.

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
Qed.

Set Implicit Arguments.

Record reified A := Reified {
  reify_trm : forall Γ t, realizes Γ A t -> term;
  reify_typ : forall Γ t (r : realizes Γ A t), [ Γ ⊢nf (reify_trm Γ t r) : A ];
  reify_cvn : forall Γ t (r : realizes Γ A t), convertible t (reify_trm Γ t r);
}.

Record interp (A : type) := {
  reflect : forall Γ t, [ Γ ⊢ne t : A ] -> eval Γ A t;
  reify : reified A;
}.

Unset Implicit Arguments.

Lemma completeness : forall A, interp A.
Proof.
induction A; split; cbn in *.
+ intros Γ t Ht; cbn in *.
  exists t; [assumption|constructor].
+ unshelve refine (@Reified _ _ _ _).
  - intros Γ t Ht; cbn in *.
    refine (Ht.(eval_atm_red)).
  - intros Γ t Ht; cbn in *.
    apply NF.typing_ne; apply Ht.
  - intros Γ t Ht; cbn in *.
    destruct Ht as [r ? Hr]; cbn.
    assumption.
+ intros Γ t Ht Δ e eε x xε.
  pose (r := IHA1.(reify).(reify_trm) _ _ xε).
  apply eval_convertible_compat with (t := (app (lift_term e t) r)).
  unfold r; rewrite <- IHA1.(reify).(reify_cvn); reflexivity.
  apply IHA2.(reflect).
  eapply NF.typing_app.
  - apply NF_typing_lift_compat with Γ; eassumption.
  - apply IHA1.(reify).
+ unshelve refine (@Reified _ _ _ _); cbn.
  - intros Γ t Ht.
    specialize (Ht (cons A1 Γ) _ (typing_ELSHFT _ _ _ _ (typing_ELID _)) (var 0)).
    unshelve refine (let Ht := Ht (IHA1.(reflect) (NF.typing_var _ _ _ _)) in _).
    { reflexivity. }
    unshelve refine ((lam ((IHA2.(reify).(@reify_trm _) (cons A1 Γ) (app _ (var 0)) _)))).
    shelve.
    apply Ht.
  - cbn; intros Γ t Ht.
    apply NF.typing_lam.
    apply IHA2.(reify).
  - cbn; intros Γ t Ht.
    etransitivity.
    2:{ apply convertible_lam, IHA2.(reify). }
    symmetry; apply convertible_step, reduction_η.
Qed.
