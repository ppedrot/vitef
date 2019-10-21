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

Inductive heq {A : Type} (x : A) : forall {B : Type} (y : B), SProp :=
| hrefl : @heq A x A x.

Notation "x ≅ y" := (heq x y) (at level 70).

Lemma J_heq : forall (A : Type) (x : A) (P : forall (y : A), x ≅ y -> Type),
  P x (hrefl _) -> forall y e, P y e.
Proof.
intros A x P p y e.
unshelve refine (
match e in @heq _ _ Z z return
  let e₀ : A ≡ Z := match e in @heq _ _ Z z return A ≡ Z with hrefl _ => srefl _ end in
  P
    (match e₀ in _ ≡ Z return Z -> A with srefl _ => fun x => x end z)
    _
with
| hrefl _ => _
end).
refine (match e₀ in _ ≡ Z return forall (z : Z) (e : x ≅ z),
      @heq A x A (match e₀ in _ ≡ Z return Z -> A with srefl _ => fun x => x end z)
      with srefl _ => fun z e => e end z e).
refine p.
Defined.

Inductive sFalse : SProp :=.
Inductive sTrue : SProp := sI.

Module Type S.

Axiom ℙ@{} : Set.
Axiom le@{} : ℙ -> ℙ -> SProp.
Axiom le_id : forall {p}, le p p.
Axiom le_cmp : forall {p q r} (α : le p q) (β : le q r), le p r.

End S.

Module Make(Import F : S).

Notation "p ≤ q" := (le p q) (at level 70, no associativity).
Notation "'!'" := (@le_id _).
Notation "α ∘ β" := (@le_cmp _ _ _ β α) (at level 35).

Notation "α · x" := (fun r (β : r ≤ _) => x r (α ∘ β)) (at level 40).

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

(*
Record El_ {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : TypeR A) := mkEl {
  el₀ : @El₀ p A;
  elε : Elε A Aε el₀;
}.
*)

Record El_ (A : Type) (B : A -> SProp) := mkEl {
  el₀ : A;
  elε : B el₀;
}.

Arguments el₀ {_ _}.
Arguments elε {_ _}.

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

Definition El {p} (A : El_ (El₀ (@Type₀ p)) (Elε _ (@Typeε p))) : Type :=
  @El_ (El₀ A.(el₀)) (Elε _ A.(elε)).

Definition Typeᶠ {p} : El_ (El₀ (@Type₀ p)) (Elε _ (@Typeε p)) :=
  mkEl _ _ (@Type₀ p) (@Typeε p).

Definition lift {p} {A Aε} q (α : q ≤ p)
  (x : El_ (El₀ A) (Elε A Aε)) : El_ (El₀ (α · A)) (Elε (α · A) (α · Aε)) :=
  mkEl _ _ (α · x.(el₀)) (α · x.(elε)).

Notation "α ∗ x" := (@lift _ _ _ _ α x) (at level 40).

Definition plift {p} {A : El Typeᶠ} {q} {α : q ≤ p} {r} (β : r ≤ q)
  (x : El (α ∗ A)) : El (α ∘ β ∗ A) :=
  mkEl _ _ (β · x.(el₀)) (β · x.(elε)).

Notation "α • x" := (@plift _ _ _ _ _ α x) (at level 40).

Definition mkel {p} (A : @El p Typeᶠ)
  (x : El₀ A.(el₀)) (xε : Elε A.(el₀) A.(elε) x) : El A.
Proof.
refine (mkEl _ _ x xε).
Defined.

Definition Arr {p} : forall
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A B => mkEl _ _ (fun q α => mkTYPE _ _ _) _).
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

Notation "A →ᶠ B" := (Arr A B) (at level 99, right associativity, B at level 200).

Definition lamᶠ {p A B q} {α : q ≤ p}
  (f : forall r (β : r ≤ q) (x : El (α ∘ β ∗ A)), El (α ∘ β ∗ B)) : El (α ∗ Arr A B).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun r (β : r ≤ q) x => (f r β x).(el₀) r !).
+ unshelve refine (fun r (β : r ≤ q) x => (f r β x).(elε) r !).
Defined.

Definition appᶠ {p A B q} {α : q ≤ p}
  (f : @El q (α ∗ Arr A B)) (x : El (α ∗ A)) : El (α ∗ B).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun q α => f.(el₀) q α (α ∗ x)).
+ unshelve refine (fun q α => f.(elε) q α (α ∗ x)).
Defined.

Goal forall p
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  f (x : El A) q (α : q ≤ p),
  (@appᶠ p A B p ! (lamᶠ f) x).(el₀) q α = (f q α (α ∗ x)).(el₀) q !.
Proof.
intros.
reflexivity.
Abort.

Goal forall p
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  f (x : El A) q (α : q ≤ p),
  (@appᶠ p A B p ! (lamᶠ f) x).(elε) q α = (f q α (α ∗ x)).(elε) q !.
Proof.
intros.
reflexivity.
Abort.

Definition wrap {A : SProp} (x : A) := x.

Definition Prod {p} : forall
  (A : @El p Typeᶠ)
  (B : @El p (Arr A Typeᶠ)),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A B => mkEl _ _ (fun q (α : q ≤ p) => mkTYPE _ _ _) _).
+ unshelve refine (fun r (β : r ≤ q) =>
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
refine (fun r (β : r ≤ q) => _).
refine (@cast q
  (fun s (γ : s ≤ q) => B.(el₀) s (α ∘ γ) (γ ∗ x))
  (fun s (γ : s ≤ q) => B.(elε) s (α ∘ γ) (γ ∗ x))
  q ! r β (f _ _ _)
).
+ refine (fun q α r β => srefl _).
Defined.

Definition dlamᶠ {p q} {α : q ≤ p}
  {A}
  {B : El (Arr A Typeᶠ)}
  (f : forall r (β : r ≤ q) (x : @El r (α ∘ β ∗ A)), @El r (@appᶠ r (α ∘ β ∗ A) (α ∘ β ∗ Typeᶠ) r ! (α ∘ β ∗ B) x))
  : El (α ∗ Prod A B).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun r (β : r ≤ q) x => (f r β x).(el₀) r !).
+ unshelve refine (fun r (β : r ≤ q) x => (f r β x).(elε) r !).
Defined.

Definition dappᶠ {p A B q} {α : q ≤ p}
  (f : @El q (α ∗ Prod A B)) (x : El (α ∗ A)) : El (appᶠ (α ∗ B) x).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun q α => f.(el₀) q α (α ∗ x)).
+ unshelve refine (fun q α => f.(elε) q α (α ∗ x)).
Defined.

Inductive nat_ {p} :=
| O_ : nat_
| S_ : forall (n : forall q (α : q ≤ p), @nat_ q), nat_.

Inductive natR {p} : (forall q (α : q ≤ p), @nat_ q) -> SProp :=
| OR : natR (fun _ _ => O_)
| SR : forall (n : forall q α, @nat_ q) (nε : natR n), natR (fun q (α : q ≤ p) => S_ (α · n)).

Definition natᶠ {p} : @El p Typeᶠ.
Proof.
unshelve refine (mkEl _ _ (fun q α => mkTYPE _ _ _) _).
+ refine (fun q α => @nat_ q).
+ refine (fun n => natR n).
+ unfold Elε; cbn; reflexivity.
Defined.

Definition Oᶠ {p} : @El p natᶠ.
Proof.
unshelve refine (mkel _ _ _).
+ refine (fun q α => O_).
+ refine (fun q α => OR).
Defined.

Definition Sᶠ {p} : @El p (Arr natᶠ natᶠ).
Proof.
unshelve refine (mkel _ _ _).
+ refine (fun q α n => S_ n.(el₀)).
+ refine (fun q α n => SR n.(el₀) _).
  apply (n.(elε) q !).
Defined.

Definition Prodᶠ {p}
  (A : @El p Typeᶠ)
  (B : forall q (α : q ≤ p), El (α ∗ A) -> @El q Typeᶠ) : @El p Typeᶠ.
Proof.
unshelve refine (Prod A (@lamᶠ _ _ _ _ ! (fun q α x => _))).
refine (B q α x).
Defined.

Ltac fold_prod :=
match goal with
| [ |- El (?α ∗ (Prodᶠ ?A ?B)) ] => change (El (Prodᶠ (α ∗ A) (α · B)))
end.

Ltac fold_lift :=
match goal with
| [ |- El (?β ∗ (?α ∗ ?A)) ] => change (El (α ∘ β ∗ A))
end.

Ltac fold_lift_in H :=
match type of H with
| El (?β ∗ (?α ∗ ?A)) => change (El (α ∘ β ∗ A)) in H
end.

Definition eta_nat₀ {p} (n₀ : @nat_ p) : @El₀ p natᶠ.(el₀).
Proof.
refine (fun q α => _).
refine (match n₀ with O_ => O_ | S_ m => S_ (α · m) end).
Defined.

Definition eta_natR {p} (n : @El p natᶠ) : @natR p (eta_nat₀ (n.(el₀) p !)).
Proof.
destruct n as [n₀ nε]; cbn.
specialize (nε p !).
change (natR n₀) in nε.
refine (
  match nε in natR n₀ return natR (eta_nat₀ (n₀ p !))
  with
  | OR => OR
  | SR m mε => SR m mε
  end
).
Defined.

Definition eta_natᶠ {p} (n₀ : @nat_ p) (nε : natR (eta_nat₀ n₀)) : @El p natᶠ.
Proof.
unshelve refine (mkel _ _ _).
+ refine (eta_nat₀ n₀).
+ refine (fun q α => _).
  set (n := eta_nat₀ n₀) in *; clearbody n.
  cbn; induction nε.
  - constructor.
  - refine (SR (α · n) IHnε).
Defined.

Lemma el₀_inj : forall A (Aε : A -> SProp) x₀ y₀ (xε : Aε x₀) (yε : Aε y₀),
  x₀ ≡ y₀ -> mkEl A Aε x₀ xε ≡ mkEl A Aε y₀ yε.
Proof.
destruct 1.
reflexivity.
Defined.

Lemma eta_natᶠ_eq : forall p n, @eta_natᶠ p (n.(el₀) p !) (eta_natR _) ≡ n.
Proof.
intros p [n₀ nε].
apply el₀_inj.
cbn.
specialize (nε p !).
change (natR n₀) in nε.
induction nε.
+ reflexivity.
+ destruct IHnε.
  reflexivity.
Defined.

Inductive natI {p} : @El p natᶠ -> Type :=
| OI : natI Oᶠ
| SI : forall n, natI n -> natI (@appᶠ _ natᶠ natᶠ _ ! Sᶠ n).

Definition natI_gen : forall p n, @natI p n.
Proof.
intros p n.
destruct (eta_natᶠ_eq _ n).
generalize (eta_natR n) as nε.
generalize (n.(el₀) p !) as n₀.
clear n.
induction n₀ as [|p m₀ IHm₀]; intros nε.
+ constructor.
+ unfold eta_natᶠ.

assert (mε : natR (eta_nat₀ m₀)).
unfold eta_natᶠ; cbn.
refine (SI _ _).

Definition nat_elimᶠ p
  (P : @El p (Arr natᶠ Typeᶠ)) :
  @El p (
  ! ∗ (appᶠ (! ∗ P) Oᶠ →ᶠ
  (Prod natᶠ
    (lamᶠ (fun q α (n : @El q (! ∘ α ∗ @natᶠ p)) =>
      Arr (appᶠ (α ∗ P) (! ∗ n))
      (appᶠ (α ∗ P) (appᶠ (! ∗ Sᶠ) n)) : El (α ∗ Typeᶠ)))) →ᶠ
  Prodᶠ natᶠ (fun q α n => appᶠ (α ∗ P) n))).
Proof.
refine (lamᶠ (fun q α pO => _)).
refine (lamᶠ (fun r β pS => _)).
refine (dlamᶠ (fun s γ n => _)).
change (El (appᶠ (α ∘ β ∘ γ ∗ P) n)).
destruct (eta_natᶠ_eq _ n).
destruct n as [n₀ nε].
cbn.
unfold eta_natR.
cbn.

destruct (n₀ s !).
specialize (nε s !).
assert (e :
    match n.(el₀) s ! with
    | O_ => fun t (δ : t ≤ s) => O_
    | S_ m => fun t (δ : t ≤ s) => S_ (δ · m)
    end ≅ n.(el₀)).
{
assert (nε : natR n.(el₀)) by refine (n.(elε) s !).
destruct nε; reflexivity.
}
revert e.
generalize (el₀ n s !) as n₀.
intros n₀; revert n.
revert n₀.
fix F 1.
intros [|m₀] n e.
(* induction n₀ as [s|s m₀ IHm]; intros n e. *)
+ change n with (mkel _ n.(el₀) n.(elε)).
  refine (J_heq _ _ (fun n _ => forall nε,
  El
    (appᶠ ((α ∘ β) ∘ γ ∗ P)
       (mkel (((! ∘ α) ∘ β) ∘ γ ∗ natᶠ) n nε))
  ) _ _ e n.(elε)).
  intros nε.
  apply (β ∘ γ ∗ pO).
+ change n with (mkel _ n.(el₀) n.(elε)).
  refine (J_heq _ _ (fun n _ => forall nε,
  El
    (appᶠ ((α ∘ β) ∘ γ ∗ P)
       (mkel (((! ∘ α) ∘ β) ∘ γ ∗ natᶠ) n nε))
  ) _ _ e n.(elε)).
  intros nε.
 unshelve epose (m := mkel natᶠ m₀ _).
  { refine (fun t δ => _).
    specialize (nε t δ); cbn in *.
    refine (match nε in natR n return
      match n t ! return SProp with
      | O_ => sTrue
      | S_ m => natR m
      end
    with OR => sI | SR _ mε => mε
    end).
  }
  change (El (appᶠ (α ∘ β ∘ γ ∗ P) (! ∗ appᶠ (! ∗ Sᶠ) m))).
  assert (v := dappᶠ (γ • pS) m).
  change (El (appᶠ (α ∘ β ∘ γ ∗ P) m →ᶠ appᶠ (α ∘ β ∘ γ ∗ P) (appᶠ (! ∗ Sᶠ) m))) in v.
  refine (appᶠ (! ∗ v) _).
  refine (F (m₀ s !) m _).
  assert (mε := m.(elε) s !).
  cbn in mε.
  change (natR m₀) in mε.
  destruct mε; reflexivity.
Defined.

Goal forall p P pO pS n,
  (dappᶠ (appᶠ (appᶠ (nat_elimᶠ p P) pO) pS) (appᶠ (! ∗ Sᶠ) n)).(el₀) p ! =
  (@appᶠ p (appᶠ (! ∗ P) n) (appᶠ (! ∗ P) (appᶠ (! ∗ Sᶠ) n)) p ! (dappᶠ pS n) (dappᶠ (appᶠ (appᶠ (nat_elimᶠ p P) pO) pS) n)).(el₀) p !.
Proof.
intros p P pO pS n.
unfold appᶠ, dappᶠ.
repeat change (el₀ (mkEl _ _ ?x _)) with x.
match goal with [ |- context (el₀ (mkEl _ _
cbv iota.
unfold Sᶠ.
cbn.
unfold dappᶠ; cbn.


unfold lift.
unfold
lazy.
reflexivity.

Inductive bool_ {p : ℙ} :=
| true_ : bool_
| false_ : bool_.

Inductive boolR {p} : (forall q (α : q ≤ p), @bool_ q) -> SProp :=
| trueR : boolR (fun q α => true_)
| falseR : boolR (fun q α => false_).

Definition boolᶠ {p} : @El p Typeᶠ.
Proof.
unshelve refine (mkEl _ _ (fun q α => mkTYPE _ _ _) _).
+ refine (fun q α => @bool_ q).
+ refine (fun b => @boolR _ b).
+ unfold Elε; cbn; reflexivity.
Defined.

Definition trueᶠ {p} : @El p boolᶠ.
Proof.
unshelve refine (mkel _ _ _).
+ refine (fun q α => @true_ q).
+ refine (fun q α => _).
  constructor.
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
unshelve refine (mkEl _ _ (fun q α => mkTYPE _ _ _) _).
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
unshelve refine (mkEl _ _ _ _).
+ refine (fun q α => inl_ (α ∗ A) (α ∗ B) (α ∗ x)).
+ refine (fun q α => inlR _ (α ∗ A) (α ∗ B) (α ∗ x)).
Defined.

Definition inrᶠ {p}
  (A : @El p Typeᶠ)
  (B : @El p Typeᶠ)
  (y : El B)
  : El (sumᶠ A B).
Proof.
unshelve refine (mkEl _ _ _ _).
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

Inductive sig_ {p} (A : @El p Typeᶠ) (B : El (Arr A Typeᶠ)) :=
| pair_ : forall (x : El A) (y : El (appᶠ B x)), sig_ A B.

Inductive sigR {p} (A : @El p Typeᶠ) (B : El (Arr A Typeᶠ)) :
  (forall q (α : q ≤ p), sig_ (α ∗ A) (α ∗ B)) -> SProp :=
| pairR : forall (x : El A) (y : El (appᶠ B x)),
  sigR A B (fun q α => pair_ (α ∗ A) (α ∗ B) (α ∗ x) (α ∗ y)).

Definition sigᶠ {p}
  (A : @El p Typeᶠ)
  (B : @El p (Arr A Typeᶠ)) : @El p Typeᶠ.
Proof.
unshelve refine (mkel Typeᶠ (fun q α => mkTYPE _ _ _) _); cbn.
+ unshelve refine (fun r β => @sig_ r (α ∘ β ∗ A) (α ∘ β ∗ B)).
+ unshelve refine (sigR (α ∗ A) (α ∗ B)).
+ unfold Elε; cbn. reflexivity.
Defined.

Definition pairᶠ {p}
  (A : @El p Typeᶠ)
  (B : @El p (Arr A Typeᶠ))
  (x : El A)
  (y : El (appᶠ B x)) : El (sigᶠ A B).
Proof.
unshelve refine (mkel _ _ _); cbn.
+ unshelve refine (fun q α => pair_ (α ∗ A) (α ∗ B) (α ∗ x) (α ∗ y)).
+ unshelve refine (fun q α => pairR (α ∗ A) (α ∗ B) (α ∗ x) (α ∗ y)).
Defined.

Inductive eq_ {p} (A : @El p Typeᶠ) (x : El A) : El A -> Type :=
| refl_  : eq_ A x x.

Inductive eqR {p} (A : @El p Typeᶠ) (x : El A) :
  forall (y : El A), (forall q (α : q ≤ p), eq_ (α ∗ A) (α ∗ x) (α ∗ y)) -> SProp :=
| reflR  : eqR A x x (fun q α => refl_ _ _).

Definition eqᶠ {p}
  (A : @El p Typeᶠ)
  (x : @El p A)
  (y : @El p A) : @El p Typeᶠ.
Proof.
unshelve refine (mkEl _ _ (fun q α => mkTYPE _ _ _) _).
+ refine (fun r (β : r ≤ q) => @eq_ r (α ∘ β ∗ A) (α ∘ β ∗ x) (α ∘ β ∗ y)).
+ refine (fun e => @eqR q (α ∗ A) (α ∗ x) (α ∗ y) e).
+ unfold Elε; cbn; reflexivity.
Defined.

End Make.

Module MP_S <: S.

Definition ℙ@{} : Set := nat -> bool.

Inductive isTrue : bool -> SProp := IsTrue : isTrue true.

Definition le@{} (p q : ℙ) : SProp := forall n, isTrue (q n) -> isTrue (p n).

Definition le_id {p} : le p p := fun n e => e.
Definition le_cmp {p q r} (α : le p q) (β : le q r) : le p r :=
  fun n e => α n (β n e).

End MP_S.

Module MP.

Import MP_S.

Include Make(MP_S).

Definition inf (p q : ℙ) : ℙ := fun n => orb (p n) (q n).

Lemma inf_fst : forall {p q}, inf p q ≤ p.
Proof.
intros p q n Hn.
unfold inf, orb.
destruct Hn; constructor.
Defined.

Lemma inf_snd : forall {p q}, inf p q ≤ q.
Proof.
intros p q n Hn.
unfold inf, orb.
destruct (p n); [constructor|assumption].
Defined.

Lemma inf_rec : forall {p q r}, r ≤ p -> r ≤ q -> r ≤ inf p q.
Proof.
intros p q r Hl Hr n Hn.
unfold le, inf, orb in *.
specialize (Hl n).
specialize (Hr n).
destruct (p n); [apply Hl; constructor|].
apply Hr; assumption.
Defined.

Lemma inf_l : forall p q r, q ≤ p -> inf q r ≤ inf p r.
Proof.
intros p q r α.
refine (inf_rec (α ∘ inf_fst) inf_snd).
Defined.

Record valid@{} (p : ℙ) : Set := mkValid { wit : nat; prf : isTrue (p wit) }.

Definition E {p} : @El p Typeᶠ.
Proof.
unshelve refine (mkEl _ _ (fun q α => mkTYPE _ _ _) _).
+ refine (fun r β => valid r).
+ refine (fun e => sTrue).
+ refine (fun q α r β => srefl _).
Defined.

(*
Lemma lift_nat {p} (n : nat) : @El p natᶠ.
Proof.
revert p; induction n as [|_ n]; intros p.
+ unshelve refine (mkel natᶠ (fun q α => O_) (fun q α => OR)).
+ unshelve refine (mkel natᶠ _ _).
  - refine (fun q α => S_ (fun r β => (n r).(el₀) r !)).
  - refine (fun q α => _); cbn.
    refine (@SR q (n q).(el₀) _).
*)

Fixpoint lift_nat {p} (n : nat) : @nat_ p :=
match n with
| O => O_
| S n => S_ (fun q α => lift_nat n)
end.

Definition lift_natε {p} (n : nat) :
  ((natᶠ).(el₀) p !).(rel) (fun q α => lift_nat n).
Proof.
induction n; cbn in *.
+ constructor.
+ refine (SR _ IHn).
Defined.

Definition purify {p} (f : @El p (Arr natᶠ boolᶠ)) (n : nat) : bool.
Proof.
pose (b := f.(el₀) p ! (mkEl (El₀  natᶠ.(el₀)) (Elε _ natᶠ.(elε)) (fun q α => lift_nat n) (fun q α => lift_natε n))).
destruct b; [left|right].
Defined.

Definition local {p}
  (f : @El p (Arr natᶠ boolᶠ))
  (A : @El p Typeᶠ) : @El p Typeᶠ.
Proof.
unshelve refine (mkEl _ _ (fun q (α : q ≤ p) => mkTYPE q _ _) _).
+ unshelve refine (fun r (β : r ≤ q) => _).
  unshelve refine (forall s (γ : s ≤ inf r (purify f)), (A.(el₀) s ((α ∘ β ∘ inf_fst ∘ γ))).(typ) s !).
+ intros x.
  unshelve refine (
    forall r (β : r ≤ inf q (purify f)), (A.(el₀) r ((inf_fst ∘ inf_l _ _ _ α ∘ β))).(rel) _).
  unshelve refine (fun s (γ : s ≤ r) => _).
  unshelve refine (cast A.(el₀) A.(elε) ((inf_fst ∘ inf_l p q (purify f) α) ∘ β) γ _).
  refine (x s (inf_fst ∘ β ∘ γ) s (inf_rec ! (inf_snd ∘ β ∘ γ))).
+ refine (fun q α r β => srefl _).
Defined.

Lemma local_ret {p}
  (f : @El p (Arr natᶠ boolᶠ))
  (A : @El p Typeᶠ)
  (x : El A) : El (local f A).
Proof.
unshelve refine (mkEl _ _ _ _).
+ refine (fun q α r β => _).
  unshelve refine (x.(el₀) _ _).
+ refine (fun q α r β => _).
  refine (x.(elε) _ _).
Defined.

Lemma local_app {p}
  (f : @El p (Arr natᶠ boolᶠ))
  (A B : @El p Typeᶠ)
  (F : El (local f (Arr A B))) :
  El (Arr (local f A) (local f B)).
Proof.
unshelve refine (mkEl _ _ _ _).
+ refine (fun q α x r β => _).
  unshelve refine (F.(el₀) _ _ _ _ _).
  unshelve refine (mkel _ _ _).
  - refine (fun s γ => _); cbn.
    refine (x.(el₀) s (inf_fst ∘ β ∘ γ) s (inf_rec ! (inf_snd ∘ β ∘ γ))).
  - refine (fun s γ => _).
    refine (x.(elε) s (inf_fst ∘ β ∘ γ) s (inf_rec ! (inf_snd ∘ β ∘ γ))).
Show Proof.
+ refine (fun q α x r β => _).
  unshelve epose (y := F.(elε) q α r β _).
  - unshelve refine (mkel _ _ _).
    { refine (fun s γ => x.(el₀) s (inf_fst ∘ β ∘ γ) s (inf_rec ! (inf_snd ∘ β ∘ γ))). }
    { refine (fun s γ => x.(elε) s (inf_fst ∘ β ∘ γ) s (inf_rec ! (inf_snd ∘ β ∘ γ))). }
  - refine y.
Defined.

Lemma local_lam {p}
  (f : @El p (Arr natᶠ boolᶠ))
  (A B : @El p Typeᶠ) :
  El (Arr (Arr (local f A) (local f B)) (local f (Arr A B))).
Proof.
unshelve refine (mkEl _ _ _ _).
+ refine (fun q α f r β x => _).
  unshelve refine (f.(el₀) r (inf_fst ∘ β) _ r (inf_rec ! (inf_snd ∘ β))).
  unshelve refine (mkEl _ _ _ _).
  - refine (fun s γ t δ => _).
    refine (x.(el₀) t (γ ∘ inf_fst ∘ δ)).
  - refine (fun s γ t δ => _).
    refine (x.(elε) t (γ ∘ inf_fst ∘ δ)).
+ refine (fun q α f r β x => _).
  cbn in *.
  unshelve epose (y := f.(elε) r (inf_fst ∘ β) _ r (inf_rec ! (inf_snd ∘ β))).
  refine (mkel
    (α ∘ (inf_fst ∘ β) ∗ local f0 A)
    (fun s γ t δ => x.(el₀) t (γ ∘ inf_fst ∘ δ))
    (fun s γ t δ => x.(elε) t (γ ∘ inf_fst ∘ δ))
  ).
  unshelve refine y.
Defined.

Lemma E_val {p} n (e : isTrue (p n)) : @El p E.
Proof.
unshelve refine (mkel _ _ _); cbn.
+ refine (fun q α => _).
  exists n; apply α, e.
+ refine (fun q α => sI).
Defined.

Definition of_nat {p} (n : nat) : @El p natᶠ.
Proof.
refine (mkel natᶠ (fun q α => lift_nat n) (fun q α => lift_natε _)).
Defined.

Lemma local_of_E {p}
  (f : @El p (Arr natᶠ boolᶠ))
  (e : @El p E)
:
  (@El p (sumᶠ E
    (sigᶠ natᶠ
      (@lamᶠ _ natᶠ Typeᶠ (fun q α n => eqᶠ boolᶠ (@appᶠ _ natᶠ boolᶠ (α ∗ f) n) trueᶠ))))).
Proof.
assert (π := e.(el₀) (inf p (purify f)) inf_fst).
destruct π as [n π].
remember (p n) as θ; destruct θ.
+ refine (inlᶠ _ _ _).
  apply (E_val n); destruct Heqθ; constructor.
+ refine (inrᶠ _ _ _).
  unshelve refine (pairᶠ _ _ (of_nat n) _).
  move π after Heqθ.
  unfold inf, orb in π.
  destruct Heqθ.
  change (El (eqᶠ boolᶠ (appᶠ f (of_nat n)) trueᶠ)).
  assert (Hrw : appᶠ f (of_nat n) = @trueᶠ p).

End MP.
