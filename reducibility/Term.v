Require Import Lia.

Inductive term :=
| var : nat -> term
| app : term -> term -> term
| lam : term -> term
| lft : term -> term
| rgt : term -> term
| cse : term -> term -> term -> term
.

Inductive lift :=
| ELID : lift
| ELSHFT : lift -> lift
| ELLFT : lift -> lift.

Fixpoint ELLFTn (n : nat) e := match n with
| 0 => e
| S n => ELLFT (ELLFTn n e)
end.

Fixpoint ELSHFTn (n : nat) e := match n with
| 0 => e
| S n => ELSHFT (ELSHFTn n e)
end.

Set Implicit Arguments.

Inductive subs (A : Type) :=
| ESID : subs A
| CONS : A -> subs A -> subs A
| SHFT : subs A -> subs A
| LIFT : subs A -> subs A
.

Unset Implicit Arguments.

Arguments ESID {_}.

Fixpoint LIFTn {A} (n : nat) (σ : subs A) := match n with
| 0 => σ
| S n => LIFT (LIFTn n σ)
end.

Fixpoint SHFTn {A} (n : nat) (σ : subs A) := match n with
| 0 => σ
| S n => SHFT (SHFTn n σ)
end.

Fixpoint reloc n el :=
match el with
| ELID => n
| ELSHFT el => S (reloc n el)
| ELLFT el =>
  match n with
  | 0 => 0
  | S n => S (reloc n el)
  end
end.

Fixpoint lift_term (el : lift) (t : term) :=
match t with
| var n => var (reloc n el)
| app t1 t2 => app (lift_term el t1) (lift_term el t2)
| lam t => lam (lift_term (ELLFT el) t)
| lft t => lft (lift_term el t)
| rgt t => rgt (lift_term el t)
| cse t u1 u2 => cse (lift_term el t) (lift_term (ELLFT el) u1) (lift_term (ELLFT el) u2)
end.

Fixpoint lift_compose (e1 e2 : lift) {struct e1} : lift :=
match e1 with
| ELID => e2
| ELSHFT e1 => ELSHFT (lift_compose e1 e2)
| ELLFT e1 =>
  match e2 with
  | ELID => ELLFT e1
  | ELSHFT e2 => ELSHFT (lift_compose e1 e2)
  | ELLFT e2 => ELLFT (lift_compose e1 e2)
  end
end.

Lemma lift_term_ELLFTn : forall t n, lift_term (ELLFTn n ELID) t = t.
Proof.
induction t; intros m; cbn; try (f_equal; intuition).
+ revert n; induction m as [|m IHm]; cbn in *; intros n.
  - reflexivity.
  - destruct n as [|n]; [reflexivity|].
    f_equal; apply IHm.
+ refine (IHt (S m)).
+ refine (IHt2 (S m)).
+ refine (IHt3 (S m)).
Qed.

Lemma lift_term_ELID : forall t, lift_term ELID t = t.
Proof.
intros.
apply (lift_term_ELLFTn t 0).
Qed.

Fixpoint expand {A} (s : subs A) (n : nat) : (A * nat) + nat :=
match s with
| ESID => inr n
| SHFT s =>
  match expand s n with
  | inl (v, k) => inl (v, S k)
  | inr n => inr (S n)
  end
| LIFT s =>
  match n with
  | 0 => inr 0
  | S n =>
    match expand s n with
    | inl (v, k) => inl (v, S k)
    | inr n => inr (S n)
    end
  end
| CONS v s =>
  match n with
  | 0 => inl (v, 0)
  | S n => expand s n
  end
end.

Definition expand_term s n :=
match expand s n with
| inl (t, k) => lift_term (ELSHFTn k ELID) t
| inr m => var m
end.

Lemma expand_term_ESID : forall n,
  expand_term ESID n = var n.
Proof.
reflexivity.
Qed.

Lemma expand_term_CONS : forall σ n x,
  expand_term (CONS x σ) n =
  match n with 0 => x | S n => expand_term σ n end.
Proof.
intros σ n x.
unfold expand_term; cbn.
destruct n as [|n]; [apply lift_term_ELID|reflexivity].
Qed.

Fixpoint subs_compose {A} (apply : subs A -> A -> A) (σ1 σ2 : subs A) {struct σ1} : subs A :=
match σ1 with
| ESID => σ2
| CONS x σ1 =>
  (fix subs_compose_CONS σ2 {struct σ2} :=
  match σ2 with
  | ESID => CONS x σ1
  | CONS y σ2 => CONS (apply (CONS x σ1) y) (subs_compose_CONS σ2)
  | SHFT σ2 => subs_compose apply σ1 σ2
  | LIFT σ2 => CONS x (subs_compose apply σ1 σ2)
  end) σ2
| SHFT σ1 => SHFT (subs_compose apply σ1 σ2)
| LIFT σ1 =>
  (fix subs_compose_LIFT σ2 {struct σ2} :=
  match σ2 with
  | ESID => LIFT σ1
  | CONS y σ2 => CONS (apply (LIFT σ1) y) (subs_compose_LIFT σ2)
  | SHFT σ2 => SHFT (subs_compose apply σ1 σ2)
  | LIFT σ2 => LIFT (subs_compose apply σ1 σ2)
  end) σ2
end.

Fixpoint subs_term (s : subs term) (t : term) : term :=
match t with
| var n => expand_term s n
| app t1 t2 => app (subs_term s t1) (subs_term s t2)
| lam t => lam (subs_term (LIFT s) t)
| lft t => lft (subs_term s t)
| rgt t => rgt (subs_term s t)
| cse t u1 u2 => cse (subs_term s t) (subs_term (LIFT s) u1) (subs_term (LIFT s) u2)
end.

Lemma subs_term_LIFTn : forall t n, subs_term (LIFTn n ESID) t = t.
Proof.
induction t; intros m; cbn.
+ revert n; induction m as [|m]; intros n; cbn.
  - reflexivity.
  - unfold expand_term; cbn; destruct n as [|n]; [reflexivity|].
    specialize (IHm n).
    unfold expand_term in IHm.
    destruct (expand (LIFTn m ESID) n) as [[v k]|p]; [|congruence].
    destruct v as [p| | | | | ]; cbn in *; congruence.
+ f_equal; intuition.
+ f_equal; apply (IHt (S m)).
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - apply (IHt2 (S m)).
  - apply (IHt3 (S m)).
Qed.

Lemma subs_term_ESID : forall t, subs_term ESID t = t.
Proof.
intros t; apply (subs_term_LIFTn t 0).
Qed.


Fixpoint subs_of_lift {A} el : subs A :=
match el with
| ELID => ESID
| ELLFT el => LIFT (subs_of_lift el)
| ELSHFT el => SHFT (subs_of_lift el)
end.

Lemma subs_term_lift : forall e t,
  subs_term (subs_of_lift e) t = lift_term e t.
Proof.
intros e t; revert e; induction t; intros e; cbn.
+ revert n; induction e; intros n; cbn.
  - reflexivity.
  - unfold expand_term; cbn.
    specialize (IHe n); unfold expand_term in IHe.
    destruct (expand (subs_of_lift e) n) as [[v k]|m]; [|congruence].
    destruct v; cbn in *; congruence.
  - destruct n as [|n]; cbn; [f_equal; apply plus_n_O|].
    unfold expand_term; cbn.
    specialize (IHe n); unfold expand_term in IHe.
    destruct (expand (subs_of_lift e) n) as [[v k]|m]; [|congruence].
    destruct v; cbn in *; congruence.
+ f_equal; intuition.
+ f_equal; apply (IHt (ELLFT e)).
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - apply (IHt2 (ELLFT e)).
  - apply (IHt3 (ELLFT e)).
Qed.

Lemma subs_lift_compose : forall e1 e2,
  subs_of_lift (lift_compose e1 e2) = subs_compose subs_term (subs_of_lift e1) (subs_of_lift e2).
Proof.
induction e1; intros e2; cbn.
+ reflexivity.
+ f_equal; intuition.
+ destruct e2; cbn; f_equal; intuition.
Qed.

Lemma lift_compose_ELID_r : forall e, lift_compose e ELID = e.
Proof.
induction e; cbn; try reflexivity.
f_equal; apply IHe.
Qed.

Lemma lift_term_compose : forall e1 e2 t,
  lift_term (lift_compose e1 e2) t =
    lift_term e1 (lift_term e2 t).
Proof.
intros e1 e2 t; revert e1 e2; induction t; intros e1 e2; cbn.
+ f_equal.
  revert n e2; induction e1; intros n e2; cbn.
  - reflexivity.
  - f_equal; apply IHe1.
  - destruct e2; cbn.
    * destruct n as [|n]; reflexivity.
    * f_equal; apply IHe1.
    * destruct n; [reflexivity|f_equal]; apply IHe1.
+ f_equal; intuition.
+ f_equal; rewrite <- IHt; reflexivity.
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - rewrite <- IHt2; reflexivity.
  - rewrite <- IHt3; reflexivity.
Qed.

Lemma expand_term_SHFT : forall σ n,
  expand_term (SHFT σ) n = lift_term (ELSHFT ELID) (expand_term σ n).
Proof.
intros; unfold expand_term; cbn.
destruct (expand σ n) as [[v k]|m]; cbn; [|reflexivity].
rewrite <- lift_term_compose; reflexivity.
Qed.

Lemma expand_term_LIFT : forall σ n,
  expand_term (LIFT σ) n =
  match n with 0 => var 0 | S n => lift_term (ELSHFT ELID) (expand_term σ n) end.
Proof.
intros; unfold expand_term; cbn; destruct n as [|n]; [reflexivity|].
destruct (expand σ n) as [[k v]|m]; cbn; [|reflexivity].
rewrite <- lift_term_compose; reflexivity.
Qed.

Lemma subs_term_CONS_SHFT_n : forall σ x t n,
  subs_term (LIFTn n (CONS x σ)) (lift_term (ELLFTn n (ELSHFT ELID)) t) = subs_term (LIFTn n σ) t.
Proof.
intros σ x t; revert σ x.
induction t; intros σ x m; cbn.
+ revert n; induction m as [|m]; intros n; cbn.
  - rewrite expand_term_CONS; reflexivity.
  - rewrite !expand_term_LIFT.
    destruct n as [|n]; [reflexivity|].
    f_equal; apply IHm.
+ f_equal; intuition.
+ f_equal.
  apply (IHt _ _ (S m)).
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - apply (IHt2 _ _ (S m)).
  - apply (IHt3 _ _ (S m)).
Qed.

Lemma subs_term_CONS_SHFT : forall σ x t,
  subs_term (CONS x σ) (lift_term (ELSHFT ELID) t) = subs_term σ t.
Proof.
intros; apply subs_term_CONS_SHFT_n with (n := 0).
Qed.

Lemma subs_term_SHFT_SHFT_n : forall σ t n,
  subs_term (LIFTn n (SHFT σ)) t = lift_term (ELLFTn n (ELSHFT ELID)) (subs_term (LIFTn n σ) t).
Proof.
intros σ t; revert σ; induction t; intros σ m; cbn.
+ revert σ n; induction m as [|m]; intros σ n; cbn.
  - rewrite expand_term_SHFT; reflexivity.
  - rewrite !expand_term_LIFT; destruct n as [|n]; [reflexivity|].
    rewrite IHm, <- !lift_term_compose; f_equal.
    clear; induction m as [|m]; cbn; congruence.
+ f_equal; intuition.
+ f_equal; apply (IHt _ (S m)).
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - apply (IHt2 _ (S m)).
  - apply (IHt3 _ (S m)).
Qed.

Lemma subs_term_SHFT_SHFT : forall σ t,
  subs_term (SHFT σ) t = lift_term (ELSHFT ELID) (subs_term σ t).
Proof.
intros; apply subs_term_SHFT_SHFT_n with (n := 0).
Qed.

Lemma subs_term_LIFT_SHFT_n : forall σ t n,
  subs_term (LIFTn n (LIFT σ)) (lift_term (ELLFTn n (ELSHFT ELID)) t) =
  lift_term (ELLFTn n (ELSHFT ELID)) (subs_term (LIFTn n σ) t).
Proof.
intros σ t; revert σ; induction t; intros σ m; cbn.
+ revert n σ; induction m as [|m]; intros n σ; cbn.
  - rewrite expand_term_LIFT; reflexivity.
  - rewrite !expand_term_LIFT; destruct n as [|n]; [reflexivity|].
    rewrite IHm.
    rewrite <- !lift_term_compose; cbn; do 2 f_equal.
    clear; induction m as [|m]; cbn; congruence.
+ f_equal; intuition.
+ f_equal; apply (IHt _ (S m)).
+ f_equal; intuition.
+ f_equal; intuition.
+ f_equal; intuition.
  - apply (IHt2 _ (S m)).
  - apply (IHt3 _ (S m)).
Qed.

Lemma subs_term_LIFT_SHFT : forall σ t,
  subs_term (LIFT σ) (lift_term (ELSHFT ELID) t) = lift_term (ELSHFT ELID) (subs_term σ t).
Proof.
intros σ t; apply subs_term_LIFT_SHFT_n with (n := 0).
Qed.

Lemma subs_term_compose : forall σ1 σ2 t,
  subs_term (subs_compose subs_term σ1 σ2) t =
    subs_term σ1 (subs_term σ2 t).
Proof.
intros σ1 σ2 t; revert σ1 σ2; induction t; intros σ1 σ2; cbn in *.
+ revert n σ2; induction σ1; intros n σ2; cbn.
  - rewrite subs_term_ESID; reflexivity.
  - revert n; induction σ2; intros n; cbn.
    * reflexivity.
    * rewrite !expand_term_CONS.
      destruct n as [|n]; [reflexivity|].
      apply IHσ2.
    * rewrite IHσ1, expand_term_SHFT, subs_term_CONS_SHFT; reflexivity.
    * rewrite !expand_term_CONS, expand_term_LIFT.
      destruct n as [|n]; cbn.
      { symmetry; apply lift_term_ELID. }
      { rewrite IHσ1, subs_term_CONS_SHFT; reflexivity. }
  - rewrite expand_term_SHFT, IHσ1; clear.
    rewrite subs_term_SHFT_SHFT; reflexivity.
  - revert n; induction σ2; intros n; cbn.
    * reflexivity.
    * rewrite !expand_term_CONS; destruct n as [|n]; [reflexivity|].
      apply IHσ2.
    * rewrite !expand_term_SHFT, IHσ1.
      rewrite subs_term_LIFT_SHFT; reflexivity.
    * rewrite !expand_term_LIFT; destruct n as [|n]; [reflexivity|].
      rewrite IHσ1.
      rewrite subs_term_LIFT_SHFT; reflexivity.
+ rewrite IHt1, IHt2; reflexivity.
+ f_equal.
  rewrite <- IHt; reflexivity.
+ f_equal; intuition.
+ f_equal; intuition.
+ rewrite <- IHt1, <- IHt2, <- IHt3; reflexivity.
Qed.
