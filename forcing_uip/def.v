Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

Notation "x ≡ y" := (seq x y) (at level 70).

(*
Axiom J_seq : forall (A : Type) (x : A) (P : forall y, x ≡ y -> Type),
  P x (srefl _) -> forall y e, P y e.
*)
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

Definition El {p : ℙ} (A : forall q (α : q ≤ p), TYPE q) :=
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
  (x : El A)
  :=
  forall q (α : q ≤ p),
    (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β))).

Definition Typeᶠ {p} : forall q (α : q ≤ p), TYPE q.
Proof.
unshelve econstructor.
+ refine (fun r β => TYPE r).
+ unshelve refine (fun A =>
  forall r (β : r ≤ q),
    (A q !).(typ) r β ≡ (A r β).(typ) r !).
Defined.

(* Hard-wired, it requires definitional UIP to type-check *)
Definition TypeR {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q) : SProp :=
  forall q (α : q ≤ p) r (β : r ≤ q),
    (A q α).(typ) r β ≡ (A r (α ∘ β) ).(typ) r !.

Definition Typeε {p} : @TypeR p Typeᶠ.
Proof.
intros q α r β.
reflexivity.
Defined.

Goal forall p A, TypeR A = @Elε p  Typeᶠ Typeε A.
Proof.
reflexivity.
Abort.

Definition Arr {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A Aε B Bε q α => mkTYPE _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x : El (α ∘ β · A))
  (xε : Elε (α ∘ β · A) (α ∘ β · Aε) x)
  ,
  (B r (α ∘ β)).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : El (α · A))
  (xε : Elε (α · A) (α · Aε) x)
  ,
  (B q α).(rel) (fun r β =>
    cast B Bε α _ (f r β (β · x) (β · xε)))
).
Defined.

Definition Arrε {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B),
  Elε Typeᶠ Typeε (Arr A Aε B Bε).
Proof.
intros A Aε B Bε q α r β.
reflexivity.
Defined.

Definition lamᶠ {p A Aε B Bε}
  (f : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x), El (α · B))
: El (Arr A Aε B Bε).
Proof.
refine (fun q α x xε => _).
unshelve refine (f q α x xε q !).
Defined.

Definition lamε {p A Aε B Bε f}
  (fε : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x),
    Elε (α · B) (α · Bε) (f q α x xε))
: Elε (Arr A Aε B Bε) (Arrε A Aε B Bε) (lamᶠ f).
Proof.
refine (fun q α x xε => _).
unshelve refine (fε q α x xε q !).
Defined.

Definition appᶠ {p A Aε B Bε} (f : @El p (Arr A Aε B Bε)) (x : El A) (xε : Elε A Aε x) : El B.
Proof.
refine (fun q α => f q α (α · x) (α · xε)).
Defined.

Definition appε {p A Aε B Bε} {f : @El p (Arr A Aε B Bε)}
  (fε : Elε _ (Arrε A Aε B Bε) f) (x : El A) (xε : Elε A Aε x) : Elε B Bε (appᶠ f x xε).
Proof.
refine (fun q α => fε _ _ (α · x) (α · xε)).
Defined.

(*
Goal forall p
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  f (x : El A) (xε : Elε A Aε x) q (α : q ≤ p),
  @appᶠ p A Aε B Bε (lamᶠ f) x xε q α = f q α (α · x) (α · xε) q !.
Proof.
reflexivity.
Abort.
*)

Definition Prod {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p (Arr A Aε Typeᶠ Typeε))
  (Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A Aε B Bε q α => mkTYPE _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x : El (α ∘ β · A))
  (xε : Elε (α ∘ β · A) (α ∘ β · Aε) x)
  ,
  (B r (α ∘ β) x xε).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : El (α · A))
  (xε : Elε (α · A) (α · Aε) x)
  ,
  (B q α x xε).(rel) _
).
unshelve refine (fun r β => @cast q
  (fun s (γ : s ≤ q) => B s (α ∘ γ) (γ · x) (γ · xε))
  (fun s (γ : s ≤ q) => Bε s (α ∘ γ) (γ · x) (γ · xε))
  _ ! _ β (f r _ (β · x) (β · xε))).
Defined.

Definition Prodε {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : El (Arr A Aε Typeᶠ Typeε))
  (Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B),
  Elε Typeᶠ Typeε (Prod A Aε B Bε)
.
Proof.
refine (fun A Aε B Bε q α r β => _).
reflexivity.
Defined.

Definition dlamᶠ {p}
  {A Aε}
  {B : El (Arr A Aε Typeᶠ Typeε)}
  {Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B}
  (f : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x), El (appᶠ (α · B) x xε))
  : El (Prod A Aε B Bε).
Proof.
refine (fun q α x xε => f q α x xε q !).
Defined.

Definition dlamε {p}
  {A Aε}
  {B : El (Arr A Aε Typeᶠ Typeε)}
  {Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B}
  {f : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x), El (appᶠ (α · B) x xε)}
  (fε : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x),
    Elε (appᶠ (α · B) x xε) (@appε q (α · A) (α · Aε) (α · Typeᶠ) (α · Typeε) (α · B) (α · Bε) x xε) (f q α x xε))
  : Elε (Prod A Aε B Bε) (Prodε A Aε B Bε) (dlamᶠ f).
Proof.
refine (fun q α x xε => fε q α x xε q !).
Defined.

Inductive sum_ {p}
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
:=
| inl_ : forall
  (x : El A)
  (xε : Elε A Aε x),
  sum_ A Aε B Bε
| inr_ : forall
  (y : El B)
  (yε : Elε B Bε y),
  sum_ A Aε B Bε
.

Inductive sumR p
  (A : @El p Typeᶠ)
  (Aε : TypeR A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  : (forall q (α : q ≤ p), @sum_ q (α · A) (α · Aε) (α · B) (α · Bε)) -> SProp :=
| inlR : forall
  (x : El A)
  (xε : Elε A Aε x),
  sumR p A Aε B Bε (fun q α => @inl_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · x) (α · xε))
| inrR : forall
  (y : El B)
  (yε : Elε B Bε y),
  sumR p A Aε B Bε (fun q α => @inr_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · y) (α · yε))
.

Definition sumᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B) : @El p Typeᶠ :=
  fun q (α : q ≤ p) => mkTYPE q
    (fun r β => @sum_ r (α ∘ β · A) (α ∘ β · Aε) (α ∘ β · B) (α ∘ β · Bε))
    (fun v => sumR q (α · A) (α · Aε) (α · B) (α · Bε) v).

Definition inlᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (x : El A)
  (xε : Elε A Aε x)

  : El (sumᶠ A Aε B Bε).
Proof.
refine (fun q α => inl_ _ _ _ _ (α · x) (α · xε)).
Defined.

Definition inrᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (y : El B)
  (yε : Elε B Bε y)

  : El (sumᶠ A Aε B Bε).
Proof.
refine (fun q α => inr_ _ _ _ _ (α · y) (α · yε)).
Defined.

Definition sumε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B) : Elε Typeᶠ Typeε (sumᶠ A Aε B Bε).
Proof.
unfold Elε; cbn.
reflexivity.
Defined.

Definition inlε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (x : El A)
  (xε : Elε A Aε x)

  : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) (inlᶠ A Aε B Bε x xε).
Proof.
refine (fun q α => inlR _ _ _ _ _ (α · x) (α · xε)).
Defined.

Definition inrε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (y : El B)
  (yε : Elε B Bε y)

  : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) (inrᶠ A Aε B Bε y yε).
Proof.
refine (fun q α => inrR _ _ _ _ _ (α · y) (α · yε)).
Defined.

Definition sum_inv {p A Aε B Bε}
  (b : @El p (sumᶠ A Aε B Bε))
  (bε : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) b) :
match b p ! with
| inl_ _ _ _ _ x xε => (fun q α => @inl_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · x) (α · xε)) ≡ b
| inr_ _ _ _ _ y yε => (fun q α => @inr_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · y) (α · yε)) ≡ b
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

Definition sum_elim p : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  (P : El (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε))
  (Pε : Elε
    (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε)
    (Arrε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε) P)

  (ul : El (Prod A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ))

  (ulε : Elε _ (Prodε A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ) ul)

  (ur : El (Prod B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ))

  (urε : Elε _ (Prodε B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ) ur)

  (b : @El p (sumᶠ A Aε B Bε))
  (bε : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) b),

 forall q (α : q ≤ p),
 (P q α (α · b) (α · bε)).(typ) q !.
Proof.
intros.
assert (be := @sum_inv p A Aε B Bε b bε).
destruct (b p !) as [x xε|y yε].
+ destruct be.
 refine (ul q α (α · x) (α · xε)).
+ destruct be.
 refine (ur q α (α · y) (α · yε)).
Defined.

Definition sum_elimε p : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  (P : El (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε))
  (Pε : Elε
    (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε)
    (Arrε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε) P)

  (ul : El (Prod A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ))

  (ulε : Elε _ (Prodε A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ) ul)

  (ur : El (Prod B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ))

  (urε : Elε _ (Prodε B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ) ur)

  (b : @El p (sumᶠ A Aε B Bε))
  (bε : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) b),

 Elε _ (appε Pε b bε) (sum_elim _ _ _ _ _ _ _ ul ulε ur urε b bε).
Proof.
intros.
intros q α; cbn.
unfold appᶠ, sum_elim.
cbn.
set (b₀ := b p !).
Abort.

Definition K p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  (x : El A)
  (xε : Elε A Aε x)
  (y : El B)
  (xε : Elε B Bε y)
  q (α : q ≤ p)
,
(A q α).(typ) q !.
Proof.
refine (fun A Aε B Bε x xε y yε q α => x q α).
Defined.

Definition Kε p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  (x : El A)
  (xε : Elε A Aε x)
  (y : El B)
  (yε : Elε B Bε y)
  q (α : q ≤ p)
,
  (A q α).(rel) (fun r β => cast A Aε α β (K p A Aε B Bε x xε y yε r (α ∘ β))).
Proof.
intros.
apply xε.
Defined.
