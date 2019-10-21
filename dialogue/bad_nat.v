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

Fixpoint eval {σ} (t : term σ) (α : nat -> nat) : interp σ :=
match t in term σ return interp σ with
| Zero => O
| Succ => Datatypes.S
| Rec _ => fun p0 pS n => nat_rec _ p0 pS n
| K _ _ => fun x y => x
| S _ _ _ => fun f g x => f x (g x)
| App _ _ t u => (eval t) α (eval u α)
| Ω => α
end.

Inductive D (A : Type) : Type :=
| ret : forall x : A, D A
| ask : nat -> (nat -> D A) -> D A
.

Fixpoint run {A} (x : D A) (α : nat -> nat) : A :=
match x with
| ret _ x => x
| ask _ n k => run (k (α n)) α
end.

Inductive Dnat :=
| DO : Dnat
| DS : Dnat -> Dnat
| Dask : nat -> (nat -> Dnat) -> Dnat.

Fixpoint bind {A B} (hB : nat -> (nat -> B) -> B) (x : D A) (f : A -> B) : B :=
match x with
| ret _ x => f x
| ask _ n k => hB n (fun m => bind hB (k m) f)
end.

Fixpoint interpD (σ : type) : Set :=
match σ with
| ℕ => Dnat
| σ → τ => interpD σ -> interpD τ
end.

Fixpoint askD σ : forall (n : nat) (k : nat -> interpD σ), interpD σ :=
match σ return nat -> (nat -> interpD σ) -> interpD σ with
| ℕ => fun n k => Dask n k
| σ → τ => fun n k x => askD τ n (fun m => k m x)
end.

Fixpoint store (n : Dnat) : D nat :=
match n with
| DO => ret _ O
| DS n => bind (ask _) (store n) (fun n => ret _ (Datatypes.S n))
| Dask n k => ask _ n (fun m => store (k m))
end.

Fixpoint nat_recD σ (p0 : interpD σ) (pS : Dnat -> interpD σ -> interpD σ) (n : Dnat) {struct n} : interpD σ :=
match n with
| DO => p0
| DS n => pS n (nat_recD σ p0 pS n)
| Dask n k => askD σ n (fun m => nat_recD σ p0 pS (k m))
end.

Fixpoint Dnat_of_nat (n : nat) : Dnat :=
match n with
| O => DO
| Datatypes.S n => DS (Dnat_of_nat n)
end.

Fixpoint evalD {σ} (t : term σ) : interpD σ :=
match t in term σ return interpD σ with
| Zero => DO
| Succ => fun n => DS n
| Rec _ => fun p0 pS n => nat_recD _ p0 pS n
| K _ _ => fun x y => x
| S _ _ _ => fun f g x => f x (g x)
| App _ _ t u => (evalD t) (evalD u)
| Ω => fun n => bind (askD ℕ) (store n) (fun n => Dask n Dnat_of_nat)
end.

Fixpoint runℕ (n : Dnat) (α : nat -> nat) : nat :=
match n with
| DO => O
| DS n => Datatypes.S (runℕ n α)
| Dask m k => runℕ (k (α m)) α
end.

Inductive Relℕ (α : nat -> nat) : nat -> Dnat -> Set :=
| Oε : Relℕ α O DO
| Sε : forall n nd, Relℕ α n nd -> Relℕ α (Datatypes.S n) (DS nd)
| askε : forall n m k, Relℕ α n (k (α m)) -> Relℕ α n (Dask m k).

Fixpoint Rel {σ} α : interp σ -> (interpD σ) -> Set :=
match σ return (interp σ) -> (interpD σ) -> Set with
| ℕ => fun n nd => Relℕ α n nd
| σ → τ => fun f fd =>
  forall (x : interp σ) (xd : interpD σ),
  Rel α x xd -> Rel α (f x) (fd xd)
end.

Lemma soundness : forall σ α (t : term σ), Rel α (eval t α) (evalD t).
Proof.
induction t; cbn.
+ constructor.
+ intros n nd nε.
  constructor; assumption.
+ intros p0 p0d p0ε pS pSd pSε n nd nε.
  induction nε; cbn in *.
  - apply p0ε.
  - apply pSε, IHnε; assumption.
  - admit.
+ intros x xd xε y yd yε; refine xε.
+ intros f fd fε g gd gε x xd xε.
  refine (fε _ _ xε _ _ (gε _ _ xε)).
+ refine (IHt1 _ _ IHt2).
+ intros n nd nε.
constructor.
  induction nε; cbn in *.
  

Admitted.

Lemma bar_thm :
  forall t : term ((ℕ → ℕ) → ℕ), {d : D nat & forall α, run d α = eval t α α}.
Proof.
intros t.
pose (t₀ := App _ _ t Ω).
exists (store (evalD t₀)); intros α.
assert (Ht := soundness _ α t₀).
cbn in *.
unfold Relℕ in Ht.
rewrite Ht.
reflexivity.
Qed.
