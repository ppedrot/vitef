Require Import dialectica.

Require List.

Module cbn.

Definition env (Γ : list prp) : prp :=
  let fold A Γ := !A ⊗ Γ in
  List.fold_right fold (atm true) Γ.

Definition subst {Γ Δ A B} (p : ⊢ Γ ⊗ A ⊸ B) (q : ⊢ Δ ⊸ A) : ⊢ Γ ⊗ Δ ⊸ B.
Proof.
destruct p as [pl pr]; destruct q as [ql qr]; split.
+ intros [wl wr]; apply pl; split; [assumption|apply ql; assumption].
+ intros y; split.
  - intros wl; apply qr, pr; assumption.
  - intros wr; apply pr; [assumption|apply ql; assumption].
Defined.

Definition env_dup {Γ} : ⊢ env Γ ⊸ env Γ ⊗ env Γ.
Proof.
split.
+ intros w; split; assumption.
+ induction Γ as [|A Γ IH]; simpl.
  - intros [kl kr]; apply kl; constructor.
  - intros [kl kr]; split.
    { intros u; apply IH; simpl; split.
      + intros w; apply (kl (u, w)); assumption.
      + intros w; apply (kr (u, w)); assumption. }
    { intros w u; specialize (kl (u, w)); specialize (kr (u, w)).
      destruct kl as [_ kl]; destruct kr as [_ kr].
      specialize (kl w u); specialize (kr w u).
      destruct (rel_decidable _ u kl); [exact kl|exact kr]. }
Defined.

(* Lemma Valid_env_dup : forall Γ, Valid (@env_dup Γ).
Proof.
intros Γ; split; intros [w [zl zr]]; apply rel_arr; intros Hr.
hnf; simpl fst in *; induction Γ as [|A Γ IH].
+ simpl; repeat constructor.
+ destruct w as [u w].
  specialize (IH w).
    destruct Hr as [Hrl Hrr].
  set (F := snd (@env_dup Γ)).
  change (snd (@env_dup Γ)) in Hrr.
  simpl in *.
  remember (zl (u, w)) as x; remember (zr (u, w)) as y.
  simpl; destruct x as [xl xr]; destruct y as [yl yr].
  simpl.
  remember (zl (u, w)) as x; remember (zr (u, w)) as y.
  specialize 


Defined.

Definition var {Γ A} : ⊢ env Γ ⊗ !A ⊸ *)

Definition app {Γ A B} (t : ⊢ env Γ ⊸ !A ⊸ B) (u : ⊢ env Γ ⊸ A) : ⊢ env Γ ⊸ B.
Proof.
destruct t as [tl tr]; destruct u as [ul ur]; simpl in *; split.
+ intros γ; exact (fst (tl γ) (ul γ)).
+ intros y.
  pose (k := ur (snd (tl γ) y (ul γ)) γ).
  refine (if rel_decidable _ γ k then tr (ul γ, y) γ else k).
Defined.

Lemma Valid_app : forall Γ A B t u, Valid t -> Valid u -> Valid (@app Γ A B t u).
Proof.
intros Γ A B [tl tr] [ul ur] [Ht] [Hu]; split.
intros [γ y]; apply rel_arr; intros Hr; simpl in *.
destruct rel_decidable; [|contradiction].
specialize (Ht (γ, (ul γ, y))); specialize (Hu (γ, snd (tl γ) y (ul γ))).
simpl in *; set (U := ul γ) in *; set (T := tl γ) in *.
destruct T as [Tl Tr]; simpl in *.
apply rel_not_not; intros Hc; tauto.
Qed.

Definition K {A B} : ⊢ !A ⊸ !B ⊸ A.
Proof.
split.
+ intros u; split.
  - intros _; exact u.
  - intros _; apply C_member.
+ intros (v, x) u; exact x.
Defined.

Lemma Valid_K : forall A B, Valid (@K A B).
Proof.
intros A B; split; intros [u [v x]]; apply rel_arr; simpl.
tauto.
Qed.

End cbn.

Module cbv.

Definition app {Γ A B} (t : ⊢ !Γ ⊸ !(A ⊸ B)) (u : ⊢ !Γ ⊸ A) : ⊢ !Γ ⊸ B.
Proof.
destruct t as [tl tr]; destruct u as [ul ur]; simpl in *; split.
+ intros γ; exact (fst (tl γ) (ul γ)).
+ intros y γ.
  pose (k := ur (snd (tl γ) y (ul γ)) γ).
  refine (if rel_decidable _ γ k then tr (ul γ, y) γ else k).
Defined.

Lemma Valid_app : forall Γ A B t u, Valid t -> Valid u -> Valid (@app Γ A B t u).
Proof.
intros Γ A B [tl tr] [ul ur] [Ht] [Hu]; split.
intros [γ y]; apply rel_arr; intros Hr; simpl in *.
destruct rel_decidable; [|contradiction].
specialize (Ht (γ, (ul γ, y))); specialize (Hu (γ, snd (tl γ) y (ul γ))).
simpl in *; set (U := ul γ) in *; set (T := tl γ) in *.
destruct T as [Tl Tr]; simpl in *.
apply rel_not_not; intros Hc; tauto.
Qed.