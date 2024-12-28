Require Import Lia.

Definition eqn {A : nat -> Type} (f g : forall n : nat, A n) (n : nat) :=
  forall m, m < n -> f m = g m.

Definition continuous {A R} (f : (forall n : nat, A n) -> R) :=
  forall (α : forall n, A n), {n : nat | forall β, eqn α β n -> f α = f β}.

Section Paradox.

Variable continuity : forall (f : (nat -> nat) -> nat), continuous f.

Definition modulus f := proj1_sig (continuity f (fun _ => 0)).

Lemma modulus_spec : forall (f : (nat -> nat) -> nat),
  forall α, eqn (fun _ => 0) α (modulus f) -> f (fun _ => 0) = f α.
Proof.
unfold modulus; intros f α H.
destruct continuity as [n Hn]; cbn in *.
now apply Hn.
Qed.

Definition m₀ : nat := modulus (fun α => 0).

Definition diagonal (α : nat -> nat) : nat :=
  modulus (fun β => α (β m₀)).

Lemma diagonal_spec : forall α, eqn (fun _ => 0) α (modulus diagonal) -> m₀ = diagonal α.
Proof.
intros α H.
change m₀ with (diagonal (fun _ => 0)).
apply modulus_spec, H.
Qed.

Lemma lemma2 : forall α β, eqn (fun _ => 0) α (diagonal β) -> β 0 = β (α m₀).
Proof.
cbn; intros α β H.
apply (modulus_spec (fun γ => β (γ m₀))).
apply H.
Qed.

Let β₀ := fun n => if Nat.leb n (modulus diagonal) then 0 else 1.

Lemma lemma3 : m₀ = diagonal β₀.
Proof.
apply diagonal_spec.
intros n Hn.
unfold β₀.
rewrite Compare_dec.leb_correct; [reflexivity|lia].
Qed.

Lemma lemma4 : forall α, eqn (fun _ : nat => 0) α m₀ -> β₀ 0 = β₀ (α m₀).
Proof.
intros α H.
apply lemma2.
rewrite <- lemma3.
exact H.
Qed.

Lemma paradox : False.
Proof.
pose (α₀ := fun n => if Nat.leb (S n) m₀ then 0 else (S (modulus diagonal))).
unshelve epose proof (lemma4 α₀ _).
{ unfold α₀; intros n Hn.
  rewrite Compare_dec.leb_correct; [reflexivity|lia]. }
unfold α₀, β₀ in H.
rewrite (Compare_dec.leb_correct 0) in H; [|lia].
rewrite (Compare_dec.leb_correct_conv m₀ (S m₀)) in H; [|lia].
rewrite (Compare_dec.leb_correct_conv) in H; [|lia].
congruence.
Qed.

End Paradox.
