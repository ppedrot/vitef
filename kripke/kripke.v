(** Completeness proof of Kripke-CPS semantics in the style of Danko Iliḱ.
    Contrarily to the latter, this variant is call-by-name, uses Krivine
    CPS and makes stacks explicit. *)

Require List.

Set Primitive Projections.

Inductive formula :=
| atm : nat -> formula
| imp : formula -> formula -> formula
| sum : formula -> formula -> formula
| bot : formula
.

Notation "A → B" := (imp A B) (at level 60, right associativity).
Notation "A + B" := (sum A B) (at level 50, left associativity).

Module Proof.

Set Implicit Arguments.

Inductive proof : list formula -> formula -> Type :=
| axm : forall Γ A, proof (cons A Γ) A
| wkn : forall Γ A B, proof Γ A -> proof (cons B Γ) A
| imp_i : forall Γ A B, proof (cons A Γ) B -> proof Γ (imp A B)
| imp_e : forall Γ A B, proof Γ (imp A B) -> proof Γ A -> proof Γ B
| sum_i_l : forall Γ A B, proof Γ A -> proof Γ (sum A B)
| sum_i_r : forall Γ A B, proof Γ B -> proof Γ (sum A B)
| sum_e : forall Γ A B C, proof Γ (sum A B) -> proof (cons A Γ) C -> proof (cons B Γ) C -> proof Γ C
| bot_e: forall Γ C, proof Γ bot -> proof Γ C
.

End Proof.

Import Proof.

Module NF_Proof.

Set Implicit Arguments.

Inductive ne_proof : list formula -> formula -> Type :=
| axm : forall Γ A, List.In A Γ -> ne_proof Γ A
| imp_e : forall Γ A B, ne_proof Γ (imp A B) -> nf_proof Γ A -> ne_proof Γ B
| sum_e : forall Γ A B C, ne_proof Γ (sum A B) -> nf_proof (cons A Γ) C -> nf_proof (cons B Γ) C -> ne_proof Γ C
| bot_e : forall Γ C, ne_proof Γ bot -> ne_proof Γ C

with nf_proof : list formula -> formula -> Type :=
| ne : forall Γ A, ne_proof Γ A -> nf_proof Γ A
| imp_i : forall Γ A B, nf_proof (cons A Γ) B -> nf_proof Γ (imp A B)
| sum_i_l : forall Γ A B, nf_proof Γ A -> nf_proof Γ (sum A B)
| sum_i_r : forall Γ A B, nf_proof Γ B -> nf_proof Γ (sum A B)
.

End NF_Proof.

Notation "[ Γ ⊢ A ]" := (proof Γ A).
Notation "[ Γ ⊢ne A ]" := (NF_Proof.ne_proof Γ A).
Notation "[ Γ ⊢nf A ]" := (NF_Proof.nf_proof Γ A).

Definition formula_eq_dec : forall A B : formula, {A = B} + {A <> B}.
Proof.
induction A as [X|A HA B HB|A HA B HB|]; intros [Y|C D|C D|];
try (right; now discriminate).
+ destruct (PeanoNat.Nat.eq_dec X Y); [left; intuition|right; congruence].
+ destruct (HA C); [|right; congruence].
  destruct (HB D); [|right; congruence].
  left; congruence.
+ destruct (HA C); [|right; congruence].
  destruct (HB D); [|right; congruence].
  left; congruence.
+ left; congruence.
Defined.

Fixpoint ne_inject {Γ A} (π : [Γ ⊢ne A]) : [Γ ⊢ A]
with nf_inject {Γ A} (π : [Γ ⊢nf A]) : [Γ ⊢ A].
Proof.
{
  refine (
  match π in [Γ ⊢ne A] return [Γ ⊢ A] with
  | @NF_Proof.axm Γ A p => _
  | @NF_Proof.imp_e Γ A B π ρ => _
  | @NF_Proof.sum_e Γ A B C π ρ₁ ρ₂ => _
  | @NF_Proof.bot_e Γ C π => _
  end).
  + clear - p; induction Γ as [|B Γ IHΓ].
    - elim p.
    - destruct (formula_eq_dec B A).
      { destruct e; apply axm. }
      { apply wkn, IHΓ; destruct p; [contradiction|assumption]. }
  + eapply imp_e; [apply ne_inject, π|apply nf_inject, ρ].
  + apply sum_e with A B.
    - apply ne_inject; assumption.
    - apply nf_inject; assumption.
    - apply nf_inject; assumption.
  + apply bot_e; apply ne_inject; assumption.
}
{
  refine (
  match π in [Γ ⊢nf A] return [Γ ⊢ A] with
  | @NF_Proof.ne Γ A π => _
  | @NF_Proof.imp_i Γ A B π => _
  | @NF_Proof.sum_i_l Γ A B π => _
  | @NF_Proof.sum_i_r Γ A B π => _
  end).
  + apply ne_inject, π.
  + apply imp_i, nf_inject, π.
  + apply sum_i_l, nf_inject, π.
  + apply sum_i_r, nf_inject, π.
}
Defined.

Module Frame.

Record t := {
  set : Type;
  rel  : set -> set -> Prop;
  rel_refl : forall α, rel α α;
  rel_trans : forall α β γ, rel α β -> rel β γ -> rel α γ;
  bot : set -> formula -> Type;
}.

End Frame.

Notation "{{ A }}" := (Frame.set A).

Definition instance {F : Frame.t} := nat -> {{F}} -> Type.

Section Kripke_Soundness.

Variable F : Frame.t.

Notation "α ≤ β" := (Frame.rel F α β) (at level 50).
Notation "α ⊥ R" := (Frame.bot F α R) (at level 10).

Fixpoint ceval (ρ : instance) (A : formula) (α : F.(Frame.set)) (R : formula) {struct A} : Type :=
match A with
| atm n => forall β, β ≤ α -> ρ n β -> F.(Frame.bot) β R
| imp A B => (forall S β, β ≤ α -> ceval ρ A β S -> F.(Frame.bot) β S) * ceval ρ B α R
| sum A B =>
  (forall β, β ≤ α -> (forall S γ, γ ≤ β -> ceval ρ A γ S -> γ ⊥ S) -> β ⊥ R) *
  (forall β, β ≤ α -> (forall S γ, γ ≤ β -> ceval ρ B γ S -> γ ⊥ S) -> β ⊥ R)
| bot => unit
end.

Definition seval (ρ : instance) (A : formula) (α : F.(Frame.set)) :=
  forall R β, β ≤ α -> ceval ρ A β R -> β ⊥ R.

Fixpoint eval_env ρ (Γ : list formula) α : Type :=
match Γ with
| nil => unit
| cons A Γ => prod (eval_env ρ Γ α) (seval ρ A α)
end.

Lemma lift_env : forall ρ Γ α β, β ≤ α -> eval_env ρ Γ α -> eval_env ρ Γ β.
Proof.
induction Γ as [|A Γ]; cbn in *; intros α β p.
+ intros []; constructor.
+ intros [? x]; split.
  - apply (IHΓ α); assumption.
  - intros R γ q; apply x; eapply Frame.rel_trans; eassumption.
Defined.

Lemma lift_ceval : forall ρ A α β R, β ≤ α -> ceval ρ A α R -> ceval ρ A β R.
Proof.
induction A; intros α β R p ξ; cbn in *.
+ intros γ q e; apply ξ, e.
  apply Frame.rel_trans with β; assumption.
+ split.
  - intros S γ q ζ; apply ξ; [|assumption].
  apply Frame.rel_trans with β; assumption.
  - apply IHA2 with α; [assumption|apply ξ].
+ split.
  - intros γ q ζ. apply (fst ξ), ζ.
   apply Frame.rel_trans with β; assumption.
  - intros γ q ζ. apply (snd ξ), ζ.
   apply Frame.rel_trans with β; assumption.
+ exact tt.
Defined.

Lemma soundness : forall ρ Γ A α R, [Γ ⊢ A] -> eval_env ρ Γ α -> ceval ρ A α R -> F.(Frame.bot) α R.
Proof.
intros ρ Γ A α R π; revert α R; induction π; intros α R; cbn in *.
+ intros [γ x]; apply x, Frame.rel_refl.
+ intros [γ _]; apply IHπ, γ.
+ intros γ [x ξ].
  apply IHπ; [split|].
  - apply γ.
  - exact x.
  - assumption.
+ intros γ ξ.
  apply IHπ1; [apply γ|split]; [|assumption].
  intros S β p; apply IHπ2; eapply lift_env; eassumption.
+ intros γ [ξ₁ ξ₂].
  apply ξ₁; [apply Frame.rel_refl|]; intros S β p; apply IHπ, lift_env with α, γ; assumption.
+ intros γ [ξ₁ ξ₂].
  apply ξ₂; [apply Frame.rel_refl|]; intros S β p; apply IHπ, lift_env with α, γ; assumption.
+ intros γ ξ.
  apply (IHπ1 _ _ γ); split.
  - intros β p x; apply IHπ2; [split|].
    { apply lift_env with α; assumption. }
    { intros S δ q ζ; apply x; assumption. }
    { apply lift_ceval with α; assumption. }
  - intros β p x; apply IHπ3; [split|].
    { apply lift_env with α; assumption. }
    { intros S δ q ζ; apply x; assumption. }
    { apply lift_ceval with α; assumption. }
+ intros γ ξ.
  apply (IHπ _ _ γ tt).
Defined.

End Kripke_Soundness.

Section Kripke_Completeness.

Definition extends (Γ Δ : list formula) := forall A, List.In A Δ -> List.In A Γ.

Definition ℍ : Frame.t.
Proof.
refine {|
  Frame.set := list formula;
  Frame.rel := extends;
  Frame.bot := NF_Proof.nf_proof;
|}.
+ intros ? ? ?; assumption.
+ intros; unfold extends in *; intuition.
Defined.

Notation "α ≤ β" := (Frame.rel ℍ α β) (at level 50).

Definition ρsyn : @instance ℍ := fun n Γ => [Γ ⊢ne atm n].

Record interp A := {
  reflect : forall Γ R, [Γ ⊢ne A] -> ceval ℍ ρsyn A Γ R -> [Γ ⊢nf R];
  reify : forall Γ, seval ℍ ρsyn A Γ -> [Γ ⊢nf A];
}.

Arguments reify {A} _ {Γ}.
Arguments reflect {A} _ {Γ R}.

Lemma completeness_aux : forall A, interp A.
Proof.
induction A as [n|A IHA B IHB|A IHA B IHB|]; cbn in *.
+ split; cbn in *.
  - intros Γ R π ξ.
    refine (ξ _ _ π).
    intros X HX; assumption.
  - intros Γ π.
    apply π; [apply Frame.rel_refl|].
    intros Δ p ρ. refine (NF_Proof.ne ρ).
+ split; cbn in *.
  - intros Γ R π [x ξ].
    refine (IHB.(reflect) (NF_Proof.imp_e π (IHA.(reify) x)) ξ).
  - intros Γ π.
    refine (NF_Proof.imp_i (IHB.(reify) _)).
    intros R Δ p ξ.
    apply π.
    { intros X HX; apply p; right; assumption. }
    split; [|exact ξ].
    intros S Ξ q ζ.
    refine (IHA.(reflect) (NF_Proof.axm _ _ _) ζ).
    apply q, p; left; reflexivity.
+ split; cbn in *.
  - intros Γ R π [ξ₁ ξ₂].
    refine (NF_Proof.ne (NF_Proof.sum_e π (ξ₁ _ _ _) (ξ₂ _ _ _))).
    * intros; right; assumption.
    * intros S Δ p ζ.
      refine (IHA.(reflect) (NF_Proof.axm _ _ _) ζ).
      apply p; left; reflexivity.
    * intros; right; assumption.
    * intros S Δ p ζ.
      refine (IHB.(reflect) (NF_Proof.axm _ _ _) ζ).
      apply p; left; reflexivity.
  - intros Γ π.
    apply (π (A + B) Γ (Frame.rel_refl _ _)); split.
    { intros Δ p x.
      refine (NF_Proof.sum_i_l _ (IHA.(reify) x)). }
    { intros Δ p y.
      refine (NF_Proof.sum_i_r _ (IHB.(reify) y)). }
+ split; cbn in *.
  - intros Γ R π _.
    refine (NF_Proof.ne (NF_Proof.bot_e _ π)).
  - intros Γ π.
    refine (π _ _ (Frame.rel_refl _ _) tt).
Defined.

Lemma completeness : forall A, [nil ⊢ A] -> [nil ⊢nf A].
Proof.
intros A π.
apply completeness_aux; intros Γ Δ p ξ.
apply (soundness _ _ _ _ _ _ π tt ξ); cbn in *.
Defined.

End Kripke_Completeness.
