Require Import Omega Term Convertibility.

Inductive type :=
| atm : nat -> type
| arr : type -> type -> type
| sum : type -> type -> type.

Inductive typing : list type -> term -> type -> Type :=
| typing_var : forall Γ A n, List.nth_error Γ n = Some A -> typing Γ (var n) A
| typing_lam : forall Γ A B t, typing (cons A Γ) t B -> typing Γ (lam t) (arr A B)
| typing_app : forall Γ A B t u, typing Γ t (arr A B) -> typing Γ u A -> typing Γ (app t u) B
| typing_lft : forall Γ A B t, typing Γ t A -> typing Γ (lft t) (sum A B)
| typing_rgt : forall Γ A B t, typing Γ t B -> typing Γ (rgt t) (sum A B)
| typing_cse : forall Γ A B C t u1 u2,
  typing Γ t (sum A B) -> typing (cons A Γ) u1 C -> typing (cons B Γ) u2 C ->
  typing Γ (cse t u1 u2) C
.

Notation "[ Γ ⊢ t : A ]" := (typing Γ t A) (t at level 0).

Module NF.

Inductive shape := nf | ne.

Inductive typing : shape -> list type -> term -> type -> Type :=
| typing_ne : forall Γ A t, typing ne Γ t A -> typing nf Γ t A
| typing_var : forall Γ A n, List.nth_error Γ n = Some A -> typing ne Γ (var n) A
| typing_lam : forall Γ A B t, typing nf (cons A Γ) t B -> typing nf Γ (lam t) (arr A B)
| typing_app : forall Γ A B t u, typing ne Γ t (arr A B) -> typing nf Γ u A -> typing ne Γ (app t u) B
| typing_lft : forall Γ A B t, typing nf Γ t A -> typing nf Γ (lft t) (sum A B)
| typing_rgt : forall Γ A B t, typing nf Γ t B -> typing nf Γ (rgt t) (sum A B)
| typing_cse : forall Γ A B C t u1 u2,
  typing ne Γ t (sum A B) -> typing nf (cons A Γ) u1 C -> typing nf (cons B Γ) u2 C ->
  typing ne Γ (cse t u1 u2) C
.

End NF.

Notation "[ Γ ⊢ne t : A ]" := (NF.typing NF.ne Γ t A) (t at level 0).
Notation "[ Γ ⊢nf t : A ]" := (NF.typing NF.nf Γ t A) (t at level 0).

Inductive typing_lift : lift -> list type -> list type -> Prop :=
| typing_ELID : forall Γ, typing_lift ELID Γ Γ
| typing_ELSHFT : forall el Γ Δ A,
  typing_lift el Γ Δ ->
  typing_lift (ELSHFT el) (cons A Γ) Δ
| typing_ELLFT : forall el Γ Δ A,
  typing_lift el Γ Δ ->
  typing_lift (ELLFT el) (cons A Γ) (cons A Δ)
.

Notation "[ Γ ⊢lift e : Δ ]" := (typing_lift e Γ Δ) (e at level 0).

Lemma typing_lift_rect :
  forall P : lift -> list type -> list type -> Type,
  (forall Γ : list type, P ELID Γ Γ) ->
  (forall (el : lift) (Γ Δ : list type) (A : type),
   [Γ ⊢lift el : Δ] -> P el Γ Δ -> P (ELSHFT el) (A :: Γ)%list Δ) ->
  (forall (el : lift) (Γ Δ : list type) (A : type),
   [Γ ⊢lift el : Δ] -> P el Γ Δ -> P (ELLFT el) (A :: Γ)%list (A :: Δ)%list) ->
  forall (l : lift) (l0 l1 : list type), [l0 ⊢lift l : l1] -> P l l0 l1.
Proof.
intros P f f0 f1.
fix F 1; intros e Γ Δ He; destruct e.
+ assert (Hrw : Γ = Δ).
  { inversion He; subst; reflexivity. }
  destruct Hrw; apply f.
+ destruct Γ as [|A Γ].
  { exfalso; inversion He. }
  assert (He' : [ Γ ⊢lift e : Δ ]).
  { inversion He; subst; assumption. }
  apply f0, F; apply He'.
+ destruct Γ as [|A Γ].
  { exfalso; inversion He. }
  destruct Δ as [|B Δ].
  { exfalso; inversion He. }
  assert (Hrw : A = B).
  { inversion He; subst; reflexivity. }
  destruct Hrw.
  assert (He' : [ Γ ⊢lift e : Δ ]).
  { inversion He; subst; assumption. }
  apply f1, F; apply He'.
Qed.

Lemma nth_error_app : forall A (l1 l2 : list A) n,
  List.nth_error (l1 ++ l2)%list (length l1 + n) = List.nth_error l2 n.
Proof.
induction l1 as [|x l1]; intros l2 n; cbn.
+ reflexivity.
+ apply IHl1.
Defined.

Lemma typing_lift_reloc : forall Γ Δ A n el,
  List.nth_error Γ n = Some A ->
  typing_lift el Δ Γ -> List.nth_error Δ (reloc n el) = Some A.
Proof.
intros Γ Δ A n el e Hel.
revert n A e.
induction Hel; cbn in *; intros n B e.
+ assumption.
+ apply IHHel; assumption.
+ destruct n; cbn in *.
  - assumption.
  - apply IHHel; assumption.
Qed.

Lemma typing_lift_compat : forall Γ Δ A t el,
  typing Γ t A -> typing_lift el Δ Γ -> typing Δ (lift_term el t) A.
Proof.
intros Γ Δ A t el Ht; revert Δ el; induction Ht; intros Δ el Hel; cbn.
+ apply typing_var.
  apply typing_lift_reloc with (Γ := Γ); assumption.
+ apply typing_lam.
  apply IHHt.
  apply (typing_ELLFT _ _ _ A); assumption.
+ apply typing_app with A.
  - apply IHHt1; assumption.
  - apply IHHt2; assumption.
+ apply typing_lft, IHHt; assumption.
+ apply typing_rgt, IHHt; assumption.
+ apply typing_cse with A B.
  - apply IHHt1; assumption.
  - apply IHHt2; constructor; assumption.
  - apply IHHt3; constructor; assumption.
Qed.

Lemma NF_typing_lift_compat : forall s Γ Δ A t el,
  NF.typing s Γ t A -> typing_lift el Δ Γ -> NF.typing s Δ (lift_term el t) A.
Proof.
intros s Γ Δ A t el Ht; revert Δ el; induction Ht; intros Δ el Hel; cbn.
+ apply NF.typing_ne, IHHt, Hel.
+ apply NF.typing_var.
  apply typing_lift_reloc with (Γ := Γ); assumption.
+ apply NF.typing_lam.
  apply IHHt.
  apply (typing_ELLFT _ _ _ A); assumption.
+ apply NF.typing_app with A.
  - apply IHHt1; assumption.
  - apply IHHt2; assumption.
+ apply NF.typing_lft, IHHt; assumption.
+ apply NF.typing_rgt, IHHt; assumption.
+ apply NF.typing_cse with A B.
  - apply IHHt1; assumption.
  - apply IHHt2; constructor; assumption.
  - apply IHHt3; constructor; assumption.
Qed.

Lemma typing_lift_compose : forall Γ Δ Ξ e1 e2,
  [ Γ ⊢lift e1 : Δ ] -> [ Δ ⊢lift e2 : Ξ ] -> [ Γ ⊢lift (lift_compose e1 e2) : Ξ ].
Proof.
intros Γ Δ Ξ e1 e2 He1; revert Ξ e2; induction He1; cbn in *; intros Ξ e2 He2.
+ assumption.
+ constructor; eauto.
+ destruct e2; cbn.
  - inversion He2; subst.
    constructor; assumption.
  - inversion He2; subst.
    constructor; apply IHHe1; assumption.
  - inversion He2; subst.
    constructor; apply IHHe1; assumption.
Qed.

Inductive typing_subs : subs term -> list type -> list type -> Type :=
| typing_ESID : forall Γ, typing_subs ESID Γ Γ
| typing_CONS : forall Γ Δ s t A, typing_subs s Γ Δ -> typing Γ t A -> typing_subs (CONS t s) Γ (cons A Δ)
| typing_SHFT : forall Γ Δ s A, typing_subs s Γ Δ -> typing_subs (SHFT s) (cons A Γ) Δ
| typing_LIFT : forall Γ Δ s A, typing_subs s Γ Δ -> typing_subs (LIFT s) (cons A Γ) (cons A Δ)
.

Notation "[ Γ ⊢subs e : Δ ]" := (typing_subs e Γ Δ) (e at level 0).

Lemma typing_wkn_n : forall Γ Δ A B t,
  typing (Δ ++ Γ) t A -> typing (Δ ++ cons B Γ) (lift_term (ELLFTn (length Δ) (ELSHFT ELID)) t) A.
Proof.
intros Γ Δ A B t Ht.
remember (Δ ++ Γ)%list as Ξ; revert Γ Δ B HeqΞ.
induction Ht; cbn; intros Δ Ξ X ->.
+ constructor.
  revert n Δ e X; induction Ξ as [|D Ξ]; intros n Δ e X; cbn.
  - assumption.
  - destruct n as [|n]; cbn in *; [assumption|].
    apply IHΞ; assumption.
+ apply typing_lam.
  change (A :: (Ξ ++ X :: Δ))%list with ((cons A nil) ++ (Ξ ++ X :: Δ))%list.
  rewrite List.app_assoc.
  apply IHHt; reflexivity.
+ eapply typing_app; intuition eauto.
+ apply typing_lft; intuition eauto.
+ apply typing_rgt; intuition eauto.
+ apply typing_cse with A B.
  - intuition eauto.
  - change (A :: (Ξ ++ X :: Δ))%list with ((cons A nil) ++ (Ξ ++ X :: Δ))%list.
    rewrite List.app_assoc.
    apply IHHt2; reflexivity.
  - change (B :: (Ξ ++ X :: Δ))%list with ((cons B nil) ++ (Ξ ++ X :: Δ))%list.
    rewrite List.app_assoc.
    apply IHHt3; reflexivity.
Qed.

Lemma typing_wkn : forall Γ A B t,
  typing Γ t A -> typing (cons B Γ) (lift_term (ELSHFT ELID) t) A.
Proof.
intros.
apply typing_wkn_n with (Δ := nil); assumption.
Qed.

Lemma typing_subs_compat : forall Γ Δ A s t,
  typing Γ t A -> typing_subs s Δ Γ -> typing Δ (subs_term s t) A.
Proof.
intros Γ Δ A s t Ht; revert Δ s; induction Ht; intros Δ s Hs; cbn.
+ revert n A e; induction Hs; cbn; intros n B e.
  - constructor; assumption.
  - destruct n as [|n]; cbn in *.
    * injection e; intros ->. eapply typing_lift_compat; try eassumption.
      constructor.
    * apply IHHs; assumption.
  - specialize (IHHs _ _ e).
    unfold expand_term in *; cbn.
    destruct (expand s n) as [[v k]|m].
    change (ELSHFTn (S k) ELID) with (lift_compose (ELSHFT ELID) (ELSHFTn k ELID)).
    rewrite lift_term_compose.
    apply typing_wkn; assumption.
    constructor; inversion IHHs; subst; assumption.
  - destruct n as [|n]; cbn.
   * constructor; assumption.
   * specialize (IHHs _ _ e).
    unfold expand_term in *; cbn.
    destruct (expand s n) as [[v k]|m].
    { change (ELSHFTn (S k) ELID) with (lift_compose (ELSHFT ELID) (ELSHFTn k ELID)).
      rewrite lift_term_compose.
      apply typing_wkn; assumption. }
    { constructor; inversion IHHs; subst; assumption. }
+ constructor; apply IHHt; constructor; apply Hs.
+ apply typing_app with A; intuition.
+ apply typing_lft; intuition.
+ apply typing_rgt; intuition.
+ apply typing_cse with A B.
  - intuition.
  - apply IHHt2; constructor; assumption.
  - apply IHHt3; constructor; assumption.
Qed.

Lemma typing_subs_compose : forall Γ Δ Ξ σ1 σ2,
  [ Γ ⊢subs σ1 : Δ ] -> [ Δ ⊢subs σ2 : Ξ ] -> [ Γ ⊢subs (subs_compose subs_term σ1 σ2) : Ξ ].
Proof.
intros Γ Δ Ξ σ1 σ2 Hσ1; revert Ξ σ2; induction Hσ1; cbn in *; intros Ξ σ2 Hσ2.
+ assumption.
+ remember (A :: Δ)%list as Ω in *.
  induction Hσ2; subst.
  - constructor; assumption.
  - constructor; [apply IHHσ2; reflexivity|].
    apply typing_subs_compat with (cons A Δ); [assumption|].
    constructor; assumption.
  - apply IHHσ1.
    injection HeqΩ; intros -> ->; assumption.
  - injection HeqΩ; intros -> ->.
    constructor; [|assumption].
    apply IHHσ1; assumption.
+ constructor.
  apply IHHσ1; assumption.
+ remember (A :: Δ)%list as Ω in *.
  induction Hσ2; subst.
  - constructor; assumption.
  - constructor; [apply IHHσ2; reflexivity|].
    apply typing_subs_compat with (cons A Δ); [assumption|].
    constructor; assumption.
  - injection HeqΩ; intros -> ->.
    constructor; apply IHHσ1; assumption.
  - injection HeqΩ; intros -> ->.
    constructor.
    apply IHHσ1; assumption.
Qed.
