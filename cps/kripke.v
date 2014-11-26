Set Universe Polymorphims.

Inductive type :=
| atm : nat -> type
| arr : type -> type -> type.

Notation "A → B" := (arr A B) (at level 45, right associativity).

Inductive proof : list type -> type -> Type :=
| axm : forall Γ A, proof (A :: Γ) A
| wkn : forall Γ A B, proof Γ B -> proof (A :: Γ) B
| arr_itr : forall Γ A B, proof (A :: Γ) B -> proof Γ (A → B)
| arr_elm : forall Γ A B, proof Γ (A → B) -> proof Γ A -> proof Γ B.

Section Soundness.

Variable W : Type.
Variable le : W -> W -> Type.

Notation "x ≤ y" := (le x y) (at level 30).

Variable le_refl : forall w, le w w.
Variable le_trans : forall w1 w2 w3, le w1 w2 -> le w2 w3 -> le w1 w3.

Variable instance : nat -> W -> Type.

Fixpoint eval (t : type) (w : W) :=
match t with
| atm n => instance n w
| arr t u => (forall w', w' ≤ w -> eval t w') -> eval u w
end.

Fixpoint env_eval (Γ : list type) w : Type :=
match Γ with
| nil => unit
| cons A Γ => prod (forall w', w' ≤ w -> eval A w') (env_eval Γ w)
end.

Lemma soundness : forall Γ A, proof Γ A -> forall w, env_eval Γ w -> eval A w.
Proof.
intros Γ A p; induction p; intros w; cbn.
+ intros [x _]; apply x, le_refl.
+ intros [_ γ]; apply IHp, γ.
+ intros γ f; apply IHp; split; assumption.
+ intros γ; apply (IHp1 _ γ).
  intros w' Hw'; apply IHp2.
  clear - Hw' γ le_trans; revert w' Hw'; induction Γ; intros w' Hw'; cbn.
  - constructor.
  - destruct γ as [x γ]; split; [|apply IHΓ; assumption].
    intros w'' Hw''; apply x, le_trans with w'; assumption.
Defined.

Variable instance_monotone : forall n w1 w2, w2 ≤ w1 -> instance n w2 -> instance n w1.

Lemma monotonicity : forall A w1 w2, w2 ≤ w1 -> eval A w2 -> eval A w1.
Proof.
induction A; cbn.
+ apply instance_monotone.
+ intros w1 w2 Hw f x.
  eapply IHA2; [eassumption|]; eapply f.
  intros w3 Hw3; apply x; eapply le_trans; eassumption.
Qed.

Lemma env_monotonicity : forall Γ w1 w2, w2 ≤ w1 -> env_eval Γ w1 -> env_eval Γ w2.
Proof.
induction Γ; intros w1 w2 Hw HΓ; cbn.
+ constructor.
+ destruct HΓ as [HA HΓ].
  split; [|eapply IHΓ; eassumption].
  intros w3 Hw3.
  apply HA; eapply le_trans; eassumption.
Qed.

End Soundness.

(* Section Completeness.

Definition W := list type.

Inductive In : type -> list type -> Type :=
| Here : forall A Γ, In A (cons A Γ)
| Next : forall A B Γ, In A Γ -> In A (cons B Γ).

Definition le Γ Δ := forall A, In A Δ -> In A Γ.

Lemma le_trans : forall w1 w2 w3, le w1 w2 -> le w2 w3 -> le w1 w3.
Proof.
unfold le; intros w1 w2 w3 H12 H23; intuition.
Qed.

Lemma le_nil : forall Γ, le Γ nil.
Proof.
unfold le; inversion 1.
Qed.

Lemma le_refl : forall Γ, le Γ Γ.
Proof.
unfold le; intuition.
Qed.

Definition le_cons : forall Γ A, le (cons A Γ) Γ.
Proof.
unfold le; intros; apply Next; intuition.
Qed.

Definition instance X Γ : Type := forall Δ, le Γ Δ -> proof Δ (atm X).

Let eval A Γ := eval W le instance A Γ.
Let env_eval Γ Δ := env_eval W le instance Γ Δ.

Definition instance_monotone : forall n w1 w2, le w2 w1 -> instance n w2 -> instance n w1.
Proof.
intros n Γ Δ Hle Hn; unfold instance in *; cbn in *.
intros Ξ HΞ.
eapply Hn; eapply le_trans; eassumption.
Defined.

Lemma axiom_case : forall Δ Γ, le Δ Γ -> env_eval Γ Δ.
Proof.
induction Δ; cbn; intros Γ H.
+ destruct Γ as [|A ?]; [constructor|].
  specialize (H A (Here _ _)); inversion H.
+ 


+ constructor.
+ split.
admit.
apply IHΓ.
  - intros Δ HΔ.
    eapply soundness; [apply le_refl|apply le_trans|apply (axm nil)| ].
    eapply env_monotonicity with (w1 := cons a nil); [apply le_trans| | ].
    { intros A; inversion 1; subst; [apply HΔ; constructor|inversion H2]. }
    cbn; split; [|constructor].
    admit.
constructor.
    eapply monotonicity with (w2 := cons a nil); [apply le_trans|apply instance_monotone|apply le_cons| ].
    eapply soundness; [apply le_refl|apply le_trans|apply axm|].

  - eapply env_monotonicity; [apply le_trans|apply le_cons|apply IHΓ].

  - intros Δ HΔ.
    eapply monotonicity with (w2 := cons a Δ); [apply le_trans|apply instance_monotone| | ].
    admit.
    eapply soundness; [apply le_refl|apply le_trans|apply axm|].
       cbn.
    ++ eapply soundness; [apply le_refl|apply le_trans|apply wkn|].

Admitted.

  clear; induction Γ; cbn.
  - constructor.
  - split.
Focus 2.
+  eapply env_monotonicity; [apply le_trans|apply le_cons, le_refl|apply IHΓ].
   intros Ξ HΞ.
   eapply soundness; [apply le_refl|apply le_trans|apply axm|].
   eapply env_monotonicity; [apply le_trans| | ].



  eapply env_monotonicity; [apply le_trans|apply le_nil|].
  clear; induction Γ; cbn.
  - constructor.
  - split; [|assumption].
    clear.
    intros Δ HΔ; set (Γ := @nil type) in *; clearbody Γ; revert Δ HΔ; induction Γ; intros Δ HΔ.
    -- inversion HΔ; subst.
       eapply monotonicity; [apply le_trans|apply instance_monotone|apply le_cons, le_refl| ].
       eapply soundness; [apply le_refl|apply le_trans| |].
       apply axm.
       eapply env_monotonicity; [apply le_trans| |].

    eapply monotonicity; [apply le_trans|apply instance_monotone|apply le_cons, le_refl| ].
    eapply soundness; [apply le_refl|apply le_trans| |].
    apply axm.
    eapply env_monotonicity; [apply le_trans| |].
apply le_nil.
cbn; split; [|eassumption].

  assert (Hp : forall Δ, le Δ Γ -> env_eval Γ Δ).
  { clear; induction Γ; intros Δ HΔ.
    + constructor.
    + constructor.
      - intros Ξ HΞ.
        eapply soundness; [apply le_refl|apply le_trans|apply axm| ].
        eapply env_monotonicity; [apply le_trans|eassumption|].
        eapply env_monotonicity; [apply le_trans|eassumption|].

      - eapply env_monotonicity; [apply le_trans|eassumption|].
        apply IHΓ; constructor; apply le_refl.

  }


Lemma completeness : forall Γ A, (forall w, env_eval Γ w -> eval A w) -> proof Γ A.
Proof.
intros Γ A; revert Γ; induction A; cbn; intros Γ p.
+ eapply p; [|apply le_refl].
  apply axiom_case.
+ constructor.
  apply IHA2; cbn; intros Δ [HA HΔ].
  apply p; [apply HΔ|exact HA].
Qed.
*)
(*** FOOOO *)

Section Completeness.

Definition W := prod (list type) type.

Definition le .

Lemma le_trans : forall w1 w2 w3, le w1 w2 -> le w2 w3 -> le w1 w3.
Proof.
intros w1 w2 

Section Completeness.

Definition W := list type.

Inductive le : W -> W -> Type :=
| le_refl : forall Γ, le Γ Γ
| le_cons : forall Γ Δ A, le Γ Δ -> le (cons A Γ) Δ.

Lemma le_trans : forall w1 w2 w3, le w1 w2 -> le w2 w3 -> le w1 w3.
Proof.
intros w1 w2 w3 H12; revert w3; induction H12; intros w3.
+ intuition.
+ intros H; constructor; intuition.
Qed.

Lemma le_nil : forall Γ, le Γ nil.
Proof.
induction Γ; constructor; intuition.
Qed.

Definition instance X Γ : Type := forall Δ, le Γ Δ -> proof Δ (atm X).

Let eval A Γ := eval W le instance A Γ.
Let env_eval Γ Δ := env_eval W le instance Γ Δ.

Definition instance_monotone : forall n w1 w2, le w2 w1 -> instance n w2 -> instance n w1.
Proof.
intros n Γ Δ Hle Hn; unfold instance in *; cbn in *.
intros Ξ HΞ.
eapply Hn; eapply le_trans; eassumption.
Defined.

(* 
Fixpoint reify Γ A {struct A} : (forall w, le w Γ -> eval A w) -> proof Γ A
with reflect Γ A {struct A} : proof Γ A -> (forall w, le w Γ -> eval A w).
Proof.
+ intros f; destruct A as [n|A B].
  - apply f; apply le_refl.
  - constructor; apply reify.
    intros Δ HΔ.
    apply f.
cbn in f.
    apply f.
*)

Lemma le_inv : forall Γ Δ, le Γ Δ -> {Ξ : _ & Γ = app Ξ Δ }.
Proof.
intros Γ Δ Hle; induction Hle.
+ exists nil; reflexivity.
+ destruct IHHle as [Ξ HΞ].
  exists (A :: Ξ)%list; rewrite HΞ; cbn; reflexivity.
Qed.

Require Wellfounded.

Record complete A := {
  reify : forall Γ, (forall w, le w Γ -> eval A w) -> proof Γ A;
  reflect : forall Γ, proof Γ A -> (forall w, le Γ w -> eval A w)
}.

Lemma completeness : forall A, complete A.
Proof.
induction A; cbn; split; cbn; intros Γ.
+ intros p; apply (p Γ); apply le_refl.
+ intros p Δ HΔ; unfold instance; intros Ξ HΞ.
  assert (Hle : le Γ Ξ) by (eapply le_trans; eassumption).
  clear - Hle p.
  admit.
+ destruct IHA1 as [_ IHA1], IHA2 as [IHA2 _].
  intros p; constructor.
  apply IHA2.
  intros Δ HΔ.
  apply p.
admit.
intros 
  apply IHA1.

Lemma completeness : forall Γ A, (forall w, le Γ w -> eval A w) -> proof Γ A.
Proof.
intros Γ A p; revert Γ p; induction A; cbn; intros Γ p.
+ apply (p Γ); apply le_refl.
+ constructor.
  apply wkn.
  apply IHA2; intros Δ HΔ.
  apply p; [assumption|].
  intros Ξ HΞ.

Lemma axiom_case : forall Γ, env_eval Γ Γ.
Proof.
intros Γ.
pose (n := length Γ); assert (Hrw : n = length Γ) by reflexivity; clearbody n.
revert Γ Hrw.
assert (IH := PeanoNat.Nat.lt_wf_0 n); induction IH as [n _ IH].
destruct n as [|n]; intros Γ Hn.
+ destruct Γ; [|discriminate]; constructor.
+ destruct Γ as [|A Γ]; [discriminate|]; injection Hn; clear Hn; intros Hn.
  split.
  - intros Δ HΔ.
    destruct (le_inv Δ (A :: Γ)%list HΔ) as [Ξ HΞ]; subst Δ; clear HΔ.
    destruct Ξ as [|B Ξ]; cbn.
    {
      eapply soundness; [apply le_refl|apply le_trans|apply (axm Γ)| ].
      split.
      + intros Δ HΔ.
       eapply monotonicity; [apply le_trans|apply instance_monotone| | ].

      + eapply env_monotonicity; [apply le_trans|apply le_cons, le_refl|eapply IH; eauto].
    }
    {
      eapply soundness; [apply le_refl|apply le_trans|apply (wkn Γ)| ].

      + intros 


  - eapply env_monotonicity; [apply le_trans|apply le_cons, le_refl|eapply IH; eauto].
   intros Ξ HΞ.
   eapply soundness; [apply le_refl|apply le_trans|apply axm|].
   eapply env_monotonicity; [apply le_trans| | ].



    
    ++ eapply soundness; [apply le_refl|apply le_trans|apply axm|].
       cbn.
    ++ eapply soundness; [apply le_refl|apply le_trans|apply wkn|].

Admitted.

  clear; induction Γ; cbn.
  - constructor.
  - split.
Focus 2.
+  eapply env_monotonicity; [apply le_trans|apply le_cons, le_refl|apply IHΓ].
   intros Ξ HΞ.
   eapply soundness; [apply le_refl|apply le_trans|apply axm|].
   eapply env_monotonicity; [apply le_trans| | ].



  eapply env_monotonicity; [apply le_trans|apply le_nil|].
  clear; induction Γ; cbn.
  - constructor.
  - split; [|assumption].
    clear.
    intros Δ HΔ; set (Γ := @nil type) in *; clearbody Γ; revert Δ HΔ; induction Γ; intros Δ HΔ.
    -- inversion HΔ; subst.
       eapply monotonicity; [apply le_trans|apply instance_monotone|apply le_cons, le_refl| ].
       eapply soundness; [apply le_refl|apply le_trans| |].
       apply axm.
       eapply env_monotonicity; [apply le_trans| |].

    eapply monotonicity; [apply le_trans|apply instance_monotone|apply le_cons, le_refl| ].
    eapply soundness; [apply le_refl|apply le_trans| |].
    apply axm.
    eapply env_monotonicity; [apply le_trans| |].
apply le_nil.
cbn; split; [|eassumption].

  assert (Hp : forall Δ, le Δ Γ -> env_eval Γ Δ).
  { clear; induction Γ; intros Δ HΔ.
    + constructor.
    + constructor.
      - intros Ξ HΞ.
        eapply soundness; [apply le_refl|apply le_trans|apply axm| ].
        eapply env_monotonicity; [apply le_trans|eassumption|].
        eapply env_monotonicity; [apply le_trans|eassumption|].

      - eapply env_monotonicity; [apply le_trans|eassumption|].
        apply IHΓ; constructor; apply le_refl.

  }


Lemma completeness : forall Γ A, (forall w, env_eval Γ w -> eval A w) -> proof Γ A.
Proof.
intros Γ A; revert Γ; induction A; cbn; intros Γ p.
+ eapply p; [|apply le_refl].
  apply axiom_case.
+ constructor.
  apply IHA2; cbn; intros Δ [HA HΔ].
  apply p; [apply HΔ|exact HA].
Qed.


