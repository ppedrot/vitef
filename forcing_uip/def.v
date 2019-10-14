Set Primitive Projections.
Set Universe Polymorphism.

Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

Notation "x ≡ y" := (seq x y) (at level 70).

Axiom J_seq : forall (A : Type) (x : A) (P : forall y, x ≡ y -> Type),
  P x (srefl _) -> forall y e, P y e.

Inductive sFalse : SProp :=.

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

(*
Definition Elε {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
*)

Definition K p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  (x : El A)
  (xε : forall q (α : q ≤ p), (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β))))
  (y : El B)
  (yε : forall q (α : q ≤ p), (B q α).(rel) (fun r (β : r ≤ q) => cast B Bε α β (y r (α ∘ β))))
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
  (xε : forall q (α : q ≤ p), (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β))))
  (y : El B)
  (yε : forall q (α : q ≤ p), (B q α).(rel) (fun r (β : r ≤ q) => cast B Bε α β (y r (α ∘ β))))
  q (α : q ≤ p)
,
  (A q α).(rel) (fun r β => cast A Aε α β (K p A Aε B Bε x xε y yε r (α ∘ β))).
Proof.
intros.
apply xε.
Defined.

Definition Arr p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  q (α : q ≤ p), TYPE q.
Proof.
unshelve refine (fun A Aε B Bε q α => mkTYPE _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x : forall s (γ : s ≤ r), (A s (α ∘ β ∘ γ)).(typ) s !)
  (xε : forall s (γ : s ≤ r), (A s (α ∘ β ∘ γ)).(rel)
    (fun t (δ : t ≤ s) => cast A Aε (α ∘ β ∘ γ) δ (x t (γ ∘ δ))))
  ,
  (B r (α ∘ β)).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
  (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
    (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ))))
  ,
  (B q α).(rel) (fun r β =>
    cast B Bε α _ (f r β (β · x) (β · xε)))
).
Defined.

Definition Arrε p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  q (α : q ≤ p) r (β : r ≤ q),
  (Arr p A Aε B Bε q α).(typ) r β ≡ (Arr p A Aε B Bε r (α ∘ β)).(typ) r !.
Proof.
reflexivity.
Defined.

Definition Prod p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p)
    (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
    (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ)))),
    TYPE q)
  (Bε : forall q (α : q ≤ p)
    (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
    (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ)))),
    forall r (β : r ≤ q),
      (B q α x xε).(typ) r β ≡ (B r (α ∘ β) (β · x) (β · xε)).(typ) r !
  )
  q (α : q ≤ p), TYPE q.
Proof.
unshelve refine (fun A Aε B Bε q α => mkTYPE _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x : forall s (γ : s ≤ r), (A s (α ∘ β ∘ γ)).(typ) s !)
  (xε : forall s (γ : s ≤ r), (A s (α ∘ β ∘ γ)).(rel)
    (fun t (δ : t ≤ s) => cast A Aε (α ∘ β ∘ γ) δ (x t (γ ∘ δ))))
  ,
  (B r (α ∘ β) x xε).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
  (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
    (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ))))
  ,
  (B q α x xε).(rel) _
).
unshelve refine (fun r β => @cast q
  (fun s (γ : s ≤ q) => B s (α ∘ γ) (γ · x) (γ · xε))
  (fun s (γ : s ≤ q) => Bε s (α ∘ γ) (γ · x) (γ · xε))
  _ ! _ β (f r _ (β · x) (β · xε))).
Defined.

Definition Prodε p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p)
    (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
    (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ)))),
    TYPE q)
  (Bε : forall q (α : q ≤ p)
    (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
    (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ)))),
    forall r (β : r ≤ q),
      (B q α x xε).(typ) r β ≡ (B r (α ∘ β) (β · x) (β · xε)).(typ) r !
  )
  q (α : q ≤ p) r (β : r ≤ q),
  (Prod p A Aε B Bε q α).(typ) r β ≡ (Prod p A Aε B Bε r (α ∘ β)).(typ) r !.
Proof.
reflexivity.
Defined.

Definition Typeᶠ p : forall q (α : q ≤ p), TYPE q.
Proof.
unshelve econstructor.
+ refine (fun r β => TYPE r).
+ unshelve refine (fun A =>
  forall r (β : r ≤ q) s (γ : s ≤ r),
    (A r β).(typ) s γ ≡ (A s (β ∘ γ)).(typ) s !).
Defined.

Definition Typeε p :
  forall q (α : q ≤ p) r (β : r ≤ q),
    (Typeᶠ p q α).(typ) r β ≡ (Typeᶠ p r (α ∘ β)).(typ) r !.
Proof.
reflexivity.
Defined.

Inductive sumᶠ p
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !) :=
| inlᶠ : forall
  (x : El A)
  (xε : forall q (α : q ≤ p), (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β)))),
  sumᶠ p A Aε B Bε
| inrᶠ : forall
  (y : El B)
  (yε : forall q (α : q ≤ p), (B q α).(rel) (fun r (β : r ≤ q) => cast B Bε α β (y r (α ∘ β)))),
  sumᶠ p A Aε B Bε
.

Inductive sumε p
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  : (forall q α, sumᶠ q (α · A) (α · Aε) (α · B) (α · Bε)) -> SProp :=
| inlε : forall
  (x : El A)
  (xε : forall q (α : q ≤ p), (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β)))),
  sumε p A Aε B Bε (fun q α => inlᶠ q (α · A) (α · Aε) (α · B) (α · Bε) (α · x) (α · xε))
| inrε : forall
  (y : El B)
  (yε : forall q (α : q ≤ p), (B q α).(rel) (fun r (β : r ≤ q) => cast B Bε α β (y r (α ∘ β)))),
  sumε p A Aε B Bε (fun q α => inrᶠ q (α · A) (α · Aε) (α · B) (α · Bε) (α · y) (α · yε))
.

Definition sum_elim p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  (P : forall q (α : q ≤ p)
    (v : forall r (β : r ≤ q), sumᶠ r (α ∘ β · A) (α ∘ β · Aε) (α ∘ β · B) (α ∘ β · Bε))
    (vε : forall r (β : r ≤ q), sumε r (α ∘ β · A) (α ∘ β · Aε) (α ∘ β · B) (α ∘ β · Bε)
      (fun s (γ : s ≤ r) => (v s (β ∘ γ)))),
    TYPE q)
  (Pε : forall q (α : q ≤ p)
    (v : forall r (β : r ≤ q), sumᶠ r (α ∘ β · A) (α ∘ β · Aε) (α ∘ β · B) (α ∘ β · Bε))
    (vε : forall r (β : r ≤ q), sumε r (α ∘ β · A) (α ∘ β · Aε) (α ∘ β · B) (α ∘ β · Bε)
      (fun s (γ : s ≤ r) => (v s (β ∘ γ)))),
    forall r (β : r ≤ q),
      (P q α v vε).(typ) r β ≡ (P r (α ∘ β) (β · v) (β · vε)).(typ) r !
  )
  (ul : forall q (α : q ≤ p)
    (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
    (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ)))),
    (P q α
      (fun r β => inlᶠ r (α ∘ β · A) (α ∘ β · Aε) _ _ (β · x) (β · xε))
      (fun r β => inlε r (α ∘ β · A) (α ∘ β · Aε) _ _ (β · x) (β · xε))).(typ) q !)
  (ulε : forall q (α : q ≤ p)
    (x : forall r (β : r ≤ q), (A r (α ∘ β)).(typ) r !)
    (xε : forall r (β : r ≤ q), (A r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast A Aε (α ∘ β) γ (x s (β ∘ γ)))),
    (P q α
      (fun r β => inlᶠ r (α ∘ β · A) (α ∘ β · Aε) _ _ (β · x) (β · xε))
      (fun r β => inlε r (α ∘ β · A) (α ∘ β · Aε) _ _ (β · x) (β · xε))).(rel)
        (fun r β =>
          @cast q
            (fun s (γ : s ≤ q) => P s (α ∘ γ)
              (fun t (δ : t ≤ s) => inlᶠ t _ _ _ _ (γ ∘ δ · x) (γ ∘ δ · xε)) (fun t (δ : t ≤ s) => inlε t (α ∘ γ ∘ δ · A) (α ∘ γ ∘ δ · Aε) _ _ (γ ∘ δ · x) (γ ∘ δ · xε)))
            (fun s (γ : s ≤ q) => Pε s (α ∘ γ)
              (fun t (δ : t ≤ s) => inlᶠ t _ _ _ _ (γ ∘ δ · x) (γ ∘ δ · xε)) (fun t (δ : t ≤ s) => inlε t (α ∘ γ ∘ δ · A) (α ∘ γ ∘ δ · Aε) _ _ (γ ∘ δ · x) (γ ∘ δ · xε)))
          q ! r β (ul r (α ∘ β) (β · x) (β · xε))
        ))
  (ur : forall q (α : q ≤ p)
    (y : forall r (β : r ≤ q), (B r (α ∘ β)).(typ) r !)
    (yε : forall r (β : r ≤ q), (B r (α ∘ β)).(rel)
      (fun s (γ : s ≤ r) => cast B Bε (α ∘ β) γ (y s (β ∘ γ)))),
    (P q α
      (fun r β => inrᶠ r (α ∘ β · A) (α ∘ β · Aε) _ _ (β · y) (β · yε))
      (fun r β => inrε r (α ∘ β · A) (α ∘ β · Aε) _ _ (β · y) (β · yε))).(typ) q !)
  (b : forall q (α : q ≤ p), sumᶠ q (α · A) (α · Aε) (α · B) (α · Bε))
  (bε : forall q (α : q ≤ p), sumε q (α · A) (α · Aε) (α · B) (α · Bε) (α · b))
 q (α : q ≤ p)
,
  (P q α (α · b) (α · bε)).(typ) q !.
Proof.
intros.
Admitted.
