Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

Notation "x ≡ y" := (seq x y) (at level 70).

Lemma J_seq : forall (A : Type) (x : A) (P : forall y, x ≡ y -> Type),
  P x (srefl _) -> forall y e, P y e.
Proof.
intros A x P p y e.
refine (match e in _ ≡ z as e return P _ e with srefl _ => p end).
Defined.

Inductive sFalse : SProp :=.
Inductive sTrue : SProp := sI.

Axiom ℙ@{} : Set.
Axiom le₀@{} : ℙ -> ℙ -> Set.

Definition le p q := forall r, le₀ q r -> le₀ p r.

Definition le_id {p} : le p p := fun r k => k.
Definition le_cmp {p q r} (α : le p q) (β : le q r) : le p r := fun r k => α r (β r k).

Notation "p ≤ q" := (le p q) (at level 70, no associativity).
Notation "'!'" := (@le_id _).
Notation "α ∘ β" := (@le_cmp _ _ _ β α) (at level 35).

Notation "α · x" := (fun r β => x r (α ∘ β)) (at level 40).

Record TYPE@{i} (p : ℙ) := mkTYPE {
  typ : forall q (α : q ≤ p), Type@{i};
  rel : (forall q (α : q ≤ p), typ q α) -> SProp;
}.

Arguments typ {_}.
Arguments rel {_}.

Definition El₀ {p : ℙ} (A : forall q (α : q ≤ p), TYPE q) :=
  forall q (α : q ≤ p), (A q α).(typ) q !.

Definition cast : forall {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  {q} (α : q ≤ p) {r} (β : r ≤ q), (A r (α ∘ β)).(typ) r ! -> (A q α).(typ) r β.
Proof.
refine (fun p A Aε q α r β x => _).
refine (J_seq _ _ (fun X _ => X -> (A q α).(typ) r β) (fun r => r) _ (Aε q α r β) x).
Defined.

Definition Elε {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q),
    (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (x : El₀ A)
  :=
  forall q (α : q ≤ p),
    (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β))).

(* Hard-wired, it requires definitional UIP to type-check *)
Definition TypeR {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q) : SProp :=
  forall q (α : q ≤ p) r (β : r ≤ q),
    (A q α).(typ) r β ≡ (A r (α ∘ β) ).(typ) r !.

Record El_ {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : TypeR A) := mkEl {
  el₀ : @El₀ p A;
  elε : Elε A Aε el₀;
}.

Arguments el₀ {_ _ _}.
Arguments elε {_ _ _}.

Definition lift {p} {A Aε} q (α : q ≤ p) (x : El_ A Aε) : El_ (α · A) (α · Aε) :=
  mkEl _ _ _ (α · x.(el₀)) (α · x.(elε)).

Notation "α ∗ x" := (@lift _ _ _ _ α x) (at level 40).

Definition Type₀ {p} : forall q (α : q ≤ p), TYPE q.
Proof.
unshelve econstructor.
+ refine (fun r β => TYPE r).
+ unshelve refine (fun A =>
  forall r (β : r ≤ q),
    (A q !).(typ) r β ≡ (A r β).(typ) r !).
Defined.

Definition Typeε {p} : @TypeR p Type₀.
Proof.
intros q α r β.
reflexivity.
Defined.

Definition El {p} (A : El_ (@Type₀ p) (@Typeε p)) : Type :=
  @El_ p A.(el₀) A.(elε).

Definition Typeᶠ {p} : El_ (@Type₀ p) (@Typeε p) :=
  mkEl p (@Type₀ p) (@Typeε p) (@Type₀ p) (@Typeε p).

Definition Arr {p} : forall
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A B => mkEl _ (@Type₀ p) (@Typeε p) (fun q α => mkTYPE _ _ _) _).
+ unshelve refine (fun r β =>
  forall
  (x : El (α ∘ β ∗ A))
  ,
  (B.(el₀) r (α ∘ β)).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : El (α ∗ A))
  ,
  (B.(el₀) q α).(rel) (fun r β =>
    cast B.(el₀) B.(elε) α _ (f r β (β ∗ x)))
).
+ unfold Elε; cbn.
  reflexivity.
Defined.

Definition lamᶠ {p A B}
  (f : forall q (α : q ≤ p) (x : El (α ∗ A)), El (α ∗ B)) : El (Arr A B).
Proof.
unshelve refine (mkEl _ _ _ _ _).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(el₀) q !).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(elε) q !).
Defined.

Definition appᶠ {p A B}
  (f : @El p (Arr A B)) (x : El A) : El B.
Proof.
unshelve refine (mkEl _ _ _ _ _).
+ unshelve refine (fun q α => f.(el₀) q α (α ∗ x)).
+ unshelve refine (fun q α => f.(elε) q α (α ∗ x)).
Defined.

Goal forall p
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  f (x : El A) q (α : q ≤ p),
  (@appᶠ p A B (lamᶠ f) x).(el₀) q α = (f q α (α ∗ x)).(el₀) q !.
Proof.
intros.
reflexivity.
Abort.

Goal forall p
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  f (x : El A) q (α : q ≤ p),
  (@appᶠ p A B (lamᶠ f) x).(elε) q α = (f q α (α ∗ x)).(elε) q !.
Proof.
intros.
reflexivity.
Abort.

Definition Prod {p} : forall
  (A : @El p Typeᶠ)
  (B : @El p (Arr A Typeᶠ)),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A B => mkEl _ (@Type₀ p) (@Typeε p) (fun q α => mkTYPE _ _ _) _).
+ unshelve refine (fun r β =>
  forall
  (x : El (α ∘ β ∗ A))
  ,
  (B.(el₀) r (α ∘ β) x).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : El (α ∗ A))
  ,
  (B.(el₀) q α x).(rel) _
).
unshelve refine (fun r β => @cast q
  (fun s (γ : s ≤ q) => B.(el₀) s (α ∘ γ) (γ ∗ x))
  (fun s (γ : s ≤ q) => B.(elε) s (α ∘ γ) (γ ∗ x))
  _ ! _ β (f r _ (β ∗ x))).
+ refine (fun q α r β => srefl _).
Defined.

Definition dlamᶠ {p}
  {A}
  {B : El (Arr A Typeᶠ)}
  (f : forall q (α : q ≤ p) (x : El (α ∗ A)), El (@appᶠ _ (α ∗ A) Typeᶠ (α ∗ B) x))
  : El (Prod A B).
Proof.
unshelve refine (mkEl _ _ _ _ _).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(el₀) q !).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(elε) q !).
Defined.

Inductive sum_ {p}
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
:=
| inl_ : forall
  (x : El A),
  sum_ A B
| inr_ : forall
  (y : El B),
  sum_ A B
.

Inductive sumR p
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  : (forall q (α : q ≤ p), @sum_ q (α ∗ A) (α ∗ B)) -> SProp :=
| inlR : forall
  (x : El A),
  sumR p A B (fun q α => @inl_ q (α ∗ A) (α ∗ B) (α ∗ x))
| inrR : forall
  (y : El B),
  sumR p A B (fun q α => @inr_ q (α ∗ A) (α ∗ B) (α ∗ y))
.

Definition sumᶠ {p}
  (A : @El p Typeᶠ) (B : @El p Typeᶠ) : @El p Typeᶠ.
Proof.
unshelve refine (mkEl _ (@Type₀ p) (@Typeε p) (fun q α => mkTYPE _ _ _) _).
+ refine (fun r (β : r ≤ q) => @sum_ r (α ∘ β ∗ A) (α ∘ β ∗ B)).
+ refine (fun s => sumR q (α ∗ A) (α ∗ B) s).
+ refine (fun q α r β => srefl _).
Defined.

Definition inlᶠ {p}
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  (x : El A)
  : El (sumᶠ A B).
Proof.
unshelve refine (mkEl _ _ _ _ _).
+ refine (fun q α => inl_ (α ∗ A) (α ∗ B) (α ∗ x)).
+ refine (fun q α => inlR _ (α ∗ A) (α ∗ B) (α ∗ x)).
Defined.

Definition inrᶠ {p}
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  (y : El B)
  : El (sumᶠ A B).
Proof.
unshelve refine (mkEl _ _ _ _ _).
+ refine (fun q α => inr_ (α ∗ A) (α ∗ B) (α ∗ y)).
+ refine (fun q α => inrR _ (α ∗ A) (α ∗ B) (α ∗ y)).
Defined.

(*
Definition sum_inv {p A Aε B Bε}
  (b : El (sumᶠ A B)) :
match b.(el₀) p ! with
| inl_ _ x xε => (fun q α => @inl_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · x) (α · xε)) ≡ b
| inr_ _ y yε => (fun q α => @inr_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · y) (α · yε)) ≡ b
end.
Proof.
specialize (bε p !).
cbn in *.
assert (e : b p ! ≡ b p !) by reflexivity.
set (b₀ := b p !) in e at 2.
change (b p !) with b₀; clearbody b₀.
change (! · b) with b in bε.
destruct b₀. all: destruct bε; cbn.
+ admit.
+ elimtype sFalse.
  refine (match e in _ ≡ s return
    match s with inl_ _ _ _ _ _ _ => sFalse | inr_ _ _ _ _ _ _ => sTrue end
  with srefl _ => sI end).
+ elimtype sFalse.
  refine (match e in _ ≡ s return
    match s with inl_ _ _ _ _ _ _ => sTrue | inr_ _ _ _ _ _ _ => sFalse end
  with srefl _ => sI end).
+ admit.
Admitted.
*)

Definition sum_elim p : forall
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  (P : El (Arr (sumᶠ A B) Typeᶠ))
  (ul : El (Prod A (lamᶠ (fun q α x => @appᶠ _ (sumᶠ (α ∗ A) (α ∗ B)) (α ∗ Typeᶠ) (α ∗ P) (inlᶠ _ _ x)))))
  (ur : El (Prod B (lamᶠ (fun q α y => @appᶠ _ (sumᶠ (α ∗ A) (α ∗ B)) (α ∗ Typeᶠ) (α ∗ P) (inrᶠ _ _ y)))))
  (s : El (sumᶠ A B))
,
  El (appᶠ P s).
Proof.
intros A B P ul ur s.
admit.
Admitted.
