Inductive type : Set :=
| int : type
| arr : type -> type -> type.

Notation ℕ := int.
Notation "σ → τ" := (arr σ τ) (at level 45, right associativity).

Inductive term : type -> Set :=
| Zero : term ℕ
| Succ : term (ℕ → ℕ)
| Rec : forall σ, term (σ → (ℕ → σ → σ) → ℕ → σ)
| K : forall σ τ, term (σ → τ → σ)
| S : forall σ τ υ, term ((σ → τ → υ) → (σ → τ) → σ → υ)
| App : forall σ τ, term (σ → τ) -> term σ -> term τ
| Ω : term (ℕ → ℕ)
.

Fixpoint interp (σ : type) : Set :=
match σ with
| ℕ => nat
| σ → τ => interp σ -> interp τ
end.

Arguments nat_rec {_}.

Fixpoint eval {σ} (t : term σ) (α : nat -> nat) : interp σ :=
match t in term σ return interp σ with
| Zero => O
| Succ => Datatypes.S
| Rec _ => fun p0 pS n => nat_rec p0 pS n
| K _ _ => fun x y => x
| S _ _ _ => fun f g x => f x (g x)
| App _ _ t u => (eval t) α (eval u α)
| Ω => α
end.

Inductive D (A : Type) : Type :=
| ret : forall x : A, D A
| ask : nat -> (nat -> D A) -> D A
.

Inductive natᴰ :=
| Oᴰ : natᴰ
| Sᴰ : natᴰ -> natᴰ
| nat_ask : nat -> (nat -> natᴰ) -> natᴰ
.

Fixpoint run {A} (x : D A) (α : nat -> nat) : A :=
match x with
| ret _ x => x
| ask _ n k => run (k (α n)) α
end.

Fixpoint bind {A B} (x : D A) (f : A -> D B) : D B :=
match x with
| ret _ x => f x
| ask _ n k => ask _ n (fun m => bind (k m) f)
end.

Fixpoint nat_bind {A} (x : D A) (f : A -> natᴰ) : natᴰ :=
match x with
| ret _ x => f x
| ask _ n k => nat_ask n (fun m => nat_bind (k m) f)
end.

Fixpoint interpD (σ : type) : Set :=
match σ with
| ℕ => natᴰ
| σ → τ => interpD σ -> interpD τ
end.

Fixpoint bindD {A σ} (m : D A) : forall (f : A -> interpD σ), interpD σ :=
match σ return (A -> interpD σ) -> interpD σ with
| ℕ => fun f => nat_bind m f
| σ → τ => fun f x => bindD m (fun r => f r x)
end.

Fixpoint askD σ : forall (n : nat) (k : nat -> interpD σ), interpD σ :=
match σ return nat -> (nat -> interpD σ) -> interpD σ with
| ℕ => fun n k => nat_ask n k
| σ → τ => fun n k x => askD τ n (fun m => k m x)
end.

Fixpoint nat_recD σ (p0 : interpD σ) (pS : natᴰ -> interpD σ -> interpD σ) (n : natᴰ) {struct n} : interpD σ :=
match n with
| Oᴰ => p0
| Sᴰ n => pS n (nat_recD σ p0 pS n)
| nat_ask n k => askD σ n (fun m => nat_recD σ p0 pS (k m))
end.

Fixpoint force (n : natᴰ) : D nat :=
match n with
| Oᴰ => ret _ O
| Sᴰ n => bind (force n) (fun n => ret _ (Datatypes.S n))
| nat_ask n k => ask _ n (fun m => force (k m))
end.

Fixpoint lift (n : nat) : natᴰ :=
match n with
| O => Oᴰ
| Datatypes.S n => Sᴰ (lift n)
end.

Definition generic (n : natᴰ) : natᴰ :=
  nat_bind (force n) (fun n => nat_ask n lift).

Fixpoint evalD {σ} (t : term σ) : interpD σ :=
match t in term σ return interpD σ with
| Zero => Oᴰ
| Succ => fun n => Sᴰ n
| Rec _ => fun p0 pS n => nat_recD _ p0 pS n
| K _ _ => fun x y => x
| S _ _ _ => fun f g x => f x (g x)
| App _ _ t u => (evalD t) (evalD u)
| Ω => fun n => generic n
end.

Fixpoint nat_run (n : natᴰ) (α : nat -> nat) :=
match n with
| Oᴰ => O
| Sᴰ n => Datatypes.S (nat_run n α)
| nat_ask n k => nat_run (k (α n)) α
end.

Definition Relℕ (α : nat -> nat) (n : nat) (nd : natᴰ) := n = run (force nd) α.

Fixpoint Rel {σ} α : interp σ -> (interpD σ) -> Set :=
match σ return (interp σ) -> (interpD σ) -> Set with
| ℕ => fun n nd => Relℕ α n nd
| σ → τ => fun f fd =>
  forall (x : interp σ) (xd : interpD σ),
  Rel α x xd -> Rel α (f x) (fd xd)
end.

Lemma naturality :
  forall A B α (x : D A) (f : A -> D B),
  run (bind x f) α = run (f (run x α)) α.
Proof.
intros A B α x f; induction x; cbn.
+ reflexivity.
+ apply H.
Qed.

Lemma nat_run_run : forall n α, nat_run n α = run (force n) α.
Proof.
induction n; intros α; cbn.
+ reflexivity.
+ rewrite naturality; cbn; f_equal; apply IHn.
+ apply H.
Qed.

(* Lemma ask_arrow : *)
(*   forall σ τ n k, askD (σ → τ) n k *)

(*
Lemma kleisli : forall σ α (g : nat -> interp σ) (gd : nat -> interpD σ),
  (forall (n : nat), Rel α (g n) (gd n)) ->
  forall n nd, Relℕ α n nd -> Rel α (g n) (bindD nd gd).
Proof.
intros σ.
induction σ; intros α g gd gε n nd nε. cbn in *.
+ unfold Relℕ in *. rewrite naturality.
  rewrite nε; apply gε.
+ intros x xd xε.
  refine (IHσ2 α (fun n => g n x) _ (fun x => gε _ _ _ xε) _ _ nε).
Defined.
*)

Lemma force_lift : forall n, force (lift n) = ret _ n.
Proof.
induction n; cbn.
+ reflexivity.
+ rewrite IHn; reflexivity.
Qed.

Lemma soundness : forall σ α (t : term σ), Rel α (eval t α) (evalD t).
Proof.
induction t; cbn.
+ constructor.
+ intros n nd nε.
  unfold Relℕ in *; cbn.
  rewrite naturality.
  cbn; f_equal; assumption.
+ intros p0 p0d p0ε pS pSd pSε n nd nε.
  unfold Relℕ in nε.
  rewrite nε; clear n nε.
  induction nd as [| |n k].
  - apply p0ε.
  - cbn.
    rewrite naturality; cbn.
    apply pSε; [|assumption].
    clear.
    induction nd; cbn.
    { constructor. }
    { unfold Relℕ; reflexivity. }
    { apply H. }
  - cbn.
    specialize (H (α n)).
    admit.
+ intros x xd xε y yd yε; refine xε.
+ intros f fd fε g gd gε x xd xε.
  refine (fε _ _ xε _ _ (gε _ _ xε)).
+ refine (IHt1 _ _ IHt2).
+ intros n nd nε.
  unfold Relℕ in *.
  rewrite nε; clear n nε.
  unfold generic; cbn.
  induction nd; cbn.
  - rewrite force_lift; reflexivity.
  - rewrite naturality.
cbn.

Qed.

Lemma bar_thm :
  forall t : term ((ℕ → ℕ) → ℕ), {d : D nat & forall α, run d α = eval t α α}.
Proof.
intros t.
pose (t₀ := App _ _ t Ω).
exists ((evalD t₀)); intros α.
assert (Ht := soundness _ α t₀).
cbn in *.
unfold Relℕ in Ht.
rewrite Ht.
reflexivity.
Qed.
