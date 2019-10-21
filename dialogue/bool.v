Inductive type : Set :=
| two : type
| int : type
| arr : type -> type -> type.

Notation Bool  := two.
Notation ℕ := int.
Notation "σ → τ" := (arr σ τ) (at level 45, right associativity).

Inductive term : type -> Set :=
| Tt : term Bool
| Ff : term Bool
| If : forall σ, term (Bool → σ → σ → σ)
| Zero : term ℕ
| Succ : term (ℕ → ℕ)
| Rec : forall σ, term (σ → (ℕ → σ → σ) → ℕ → σ)
| K : forall σ τ, term (σ → τ → σ)
| S : forall σ τ υ, term ((σ → τ → υ) → (σ → τ) → σ → υ)
| App : forall σ τ, term (σ → τ) -> term σ -> term τ
| Ω : term (ℕ → Bool)
.

Fixpoint interp (σ : type) : Set :=
match σ with
| Bool => bool
| ℕ => nat
| σ → τ => interp σ -> interp τ
end.

Arguments nat_rec {_}.

Fixpoint eval {σ} (t : term σ) (α : nat -> bool) : interp σ :=
match t in term σ return interp σ with
| Tt => true
| Ff => false
| If _ => fun b t u => if b then t else u
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
| ask : nat -> (bool -> D A) -> D A
.

Fixpoint run {A} (x : D A) (α : nat -> bool) : A :=
match x with
| ret _ x => x
| ask _ n k => run (k (α n)) α
end.

Fixpoint bind {A B} (x : D A) (f : A -> D B) : D B :=
match x with
| ret _ x => f x
| ask _ n k => ask _ n (fun m => bind (k m) f)
end.

Fixpoint interpD (σ : type) : Set :=
match σ with
| Bool => D bool
| ℕ => D nat
| σ → τ => interpD σ -> interpD τ
end.

Fixpoint bindD {A σ} (m : D A) : forall (f : A -> interpD σ), interpD σ :=
match σ return (A -> interpD σ) -> interpD σ with
| Bool => fun f => bind m f
| ℕ => fun f => bind m f
| σ → τ => fun f x => bindD m (fun r => f r x)
end.

Fixpoint askD σ : forall (n : nat) (k : bool -> interpD σ), interpD σ :=
match σ return nat -> (bool -> interpD σ) -> interpD σ with
| Bool => fun n k => ask _ n k
| ℕ => fun n k => ask _ n k
| σ → τ => fun n k x => askD τ n (fun m => k m x)
end.

Definition nat_recD σ (p0 : interpD σ) (pS : D nat -> interpD σ -> interpD σ) (n : D nat) : interpD σ :=
  bindD n (fun n => nat_rec p0 (fun n r => pS (ret _ n) r) n).

Fixpoint evalD {σ} (t : term σ) : interpD σ :=
match t in term σ return interpD σ with
| Tt => ret _ true
| Ff => ret _ false
| If _ => fun b t u => bindD b (fun b => if b then t else u)
| Zero => ret _ O
| Succ => fun n => bind n (fun n => ret _ (Datatypes.S n))
| Rec _ => fun p0 pS n => nat_recD _ p0 pS n
| K _ _ => fun x y => x
| S _ _ _ => fun f g x => f x (g x)
| App _ _ t u => (evalD t) (evalD u)
| Ω => fun n => bind n (fun n => ask _ n (ret _))
end.

Inductive Relℕ (α : nat -> bool) : forall (n : nat) (nd : D nat), Set :=
| Retε : forall n, Relℕ α n (ret _ n)
| Askε : forall m n k, Relℕ α m (k (α n)) -> Relℕ α m (ask _ n k).

Inductive RelBool (α : nat -> bool) : forall (b : bool) (bd : D bool), Set :=
| RetBε : forall b, RelBool α b (ret _ b)
| AskBε : forall m n k, RelBool α m (k (α n)) -> RelBool α m (ask _ n k).

Fixpoint Rel {σ} α : interp σ -> (interpD σ) -> Set :=
match σ return (interp σ) -> (interpD σ) -> Set with
| Bool => fun b bd => RelBool α b bd
| ℕ => fun n nd => Relℕ α n nd
| σ → τ => fun f fd =>
  forall (x : interp σ) (xd : interpD σ),
  Rel α x xd -> Rel α (f x) (fd xd)
end.

Lemma kleisliℕ : forall σ α (g : nat -> interp σ) (gd : nat -> interpD σ),
  (forall (n : nat), Rel α (g n) (gd n)) ->
  forall n nd, Relℕ α n nd -> Rel α (g n) (bindD nd gd).
Proof.
intros σ.
induction σ; intros α g gd gε n nd nε. cbn in *.
+ induction nε; cbn.
  - apply gε.
  - constructor; assumption.
+ induction nε; cbn.
  - apply gε.
  - constructor; assumption.
+ intros x xd xε.
  refine (IHσ2 α (fun n => g n x) _ (fun x => gε _ _ _ xε) _ _ nε).
Defined.

Lemma kleisliB : forall σ α (g : bool -> interp σ) (gd : bool -> interpD σ),
  (forall (n : bool), Rel α (g n) (gd n)) ->
  forall n nd, RelBool α n nd -> Rel α (g n) (bindD nd gd).
Proof.
intros σ.
induction σ; intros α g gd gε n nd nε. cbn in *.
+ induction nε; cbn.
  - apply gε.
  - constructor; assumption.
+ induction nε; cbn.
  - apply gε.
  - constructor; assumption.
+ intros x xd xε.
  refine (IHσ2 α (fun n => g n x) _ (fun x => gε _ _ _ xε) _ _ nε).
Qed.

Lemma soundness : forall σ α (t : term σ), Rel α (eval t α) (evalD t).
Proof.
induction t; cbn.
+ constructor.
+ constructor.
+ intros b bd bε pt ptd ptε pf pfd pfε.
  refine (kleisliB _ _ (fun b => if b then pt else pf) _ _ _ _ _).
  - intros [|]; assumption.
  - assumption.
+ constructor.
+ intros n nd nε.
  induction nε; cbn.
  - constructor.
  - constructor.
    refine IHnε.
+ intros p0 p0d p0ε pS pSd pSε n nd nε.
  apply kleisliℕ; [|assumption].
  clear - p0ε pSε; intros n.
  induction n; cbn.
  - apply p0ε.
  - apply pSε; [|assumption].
    constructor.
+ intros x xd xε y yd yε; refine xε.
+ intros f fd fε g gd gε x xd xε.
  refine (fε _ _ xε _ _ (gε _ _ xε)).
+ refine (IHt1 _ _ IHt2).
+ intros n nd nε.
  induction nε; cbn.
  - repeat constructor.
  - constructor; assumption.
Qed.

Lemma bar_thm :
  forall t : term ((ℕ → Bool) → ℕ), {d : D nat & forall α, run d α = eval t α α}.
Proof.
intros t.
pose (t₀ := App _ _ t Ω).
exists ((evalD t₀)); intros α.
assert (Ht := soundness _ α t₀).
cbn in *.
induction Ht.
- reflexivity.
- assumption.
Qed.
