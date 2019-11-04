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

Lemma seq_sym : forall A (x y : A),
  x ≡ y -> y ≡ x.
Proof.
destruct 1; reflexivity.
Qed.

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

Lemma el₀_inj : forall p A (x y : @El p A),
  el₀ x ≡ el₀ y -> x ≡ y.
Proof.
intros p A [x₀ xε] [y₀ yε] e.
cbn in e.
destruct e.
reflexivity.
Defined.

Definition Typeᶠ {p} : El_ (El₀ (@Type₀ p)) (Elε _ (@Typeε p)) :=
  mkEl _ _ (@Type₀ p) (@Typeε p).

Definition lift {p} {A Aε} q (α : q ≤ p)
  (x : El_ (El₀ A) (Elε A Aε)) : El_ (El₀ (α · A)) (Elε (α · A) (α · Aε)) :=
  mkEl _ _ (α · x.(el₀)) (α · x.(elε)).

Notation "α ∗ x" := (@lift _ _ _ _ α x) (at level 40).

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

Definition lamᶠ {p A B}
  (f : forall q (α : q ≤ p) (x : El (α ∗ A)), El (α ∗ B)) : El (Arr A B).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(el₀) q !).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(elε) q !).
Defined.

Definition appᶠ {p A B}
  (f : @El p (Arr A B)) (x : El A) : El B.
Proof.
unshelve refine (mkEl _ _ _ _).
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

Definition dlamᶠ {p}
  {A}
  {B : El (Arr A Typeᶠ)}
  (f : forall q (α : q ≤ p) (x : El (α ∗ A)), El (@appᶠ _ (α ∗ A) Typeᶠ (α ∗ B) x))
  : El (Prod A B).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(el₀) q !).
+ unshelve refine (fun q (α : q ≤ p) x => (f q α x).(elε) q !).
Defined.

Definition dappᶠ {p}
  {A : @El p Typeᶠ}
  {B : El (Arr A Typeᶠ)}
  (f : El (Prod A B))
  (x : El A)
  : El (appᶠ B x).
Proof.
unshelve refine (mkEl _ _ _ _).
+ unshelve refine (fun q (α : q ≤ p) => f.(el₀) q α (α ∗ x)).
+ unshelve refine (fun q (α : q ≤ p) => f.(elε) q α (α ∗ x)).
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
unshelve refine (Prod A (@lamᶠ _ _ _ (fun q α x => _))).
refine (B q α x).
Defined.

Definition natη₀ {p} (n₀ : @El₀ p natᶠ.(el₀)) : @El₀ p natᶠ.(el₀) :=
match n₀ p ! with
| O_ => fun q α => O_
| S_ n₀ => fun q α => S_ (α · n₀)
end.

Lemma natε_mon {p}
  (n₀ : @El₀ p natᶠ.(el₀)) (nε : natR n₀)
  {q} (α : q ≤ p) : natR (α · n₀).
Proof.
induction nε.
+ constructor.
+ refine (SR (α · n) IHnε).
Defined.

Definition natηε {p}
  (n₀ : @El₀ p natᶠ.(el₀))
  (nε : @Elε p natᶠ.(el₀) natᶠ.(elε) n₀)
  : @Elε p natᶠ.(el₀) natᶠ.(elε) (natη₀ n₀).
Proof.
unfold El₀, Elε, natη₀ in *.
specialize (nε p !).
change (natR n₀) in nε; cbn.
intros q α.
apply natε_mon.
induction nε; cbn.
+ constructor.
+ refine (SR n nε).
Defined.

Definition natη {p} (n : @El p natᶠ) : @El p natᶠ.
Proof.
refine (mkEl _ _ (natη₀ n.(el₀)) (natηε n.(el₀) n.(elε))).
Defined.

Check (fun p => (srefl _ : @natη p Oᶠ ≡ Oᶠ)).
Check (fun p (n : @El p natᶠ) => (srefl _ : natη (appᶠ Sᶠ n) ≡ appᶠ Sᶠ n)).

Lemma natη_refl : forall p n, @natη p n ≡ n.
Proof.
intros p [n₀ nε]; cbn.
apply el₀_inj; cbn.
unfold natη₀; cbn.
specialize (nε p !).
change (natR n₀) in nε.
induction nε.
+ constructor.
+ constructor.
Defined.

Definition nat_elim_in p
  (P : @El p natᶠ -> Type)
  (uO : P Oᶠ)
  (uS : forall n, P n -> P (appᶠ Sᶠ n))
  (n : El natᶠ) :
  P n.
Proof.

refine (
  match @natη_refl p n in (_ ≡ y) return (P y) with
  | srefl _ =>
  _
  end
).

unfold natη, natη₀.
destruct n as [n₀ nε]; cbn.
generalize (natηε n₀ nε); clear nε.
unfold natη₀.
generalize (n₀ p !) as n; clear n₀.

fix F 1; intros n₀ nε.
destruct n₀ as [|m₀].
+ apply uO.
+ assert (mε : Elε natᶠ.(el₀) natᶠ.(elε) m₀).
  { refine (
      match nε p ! in natR n₀ return
        match n₀ p ! return SProp with
        | O_ => sTrue
        | S_ n₀ => forall q α, natR (α · n₀) 
        end
      with
      | OR => sI
      | SR m₀ mε => fun q α => @natε_mon p m₀ mε q α
      end
    ). }
  change nε with (fun q α => SR (α · m₀) (mε q α)).
  refine (uS (mkEl _ _ m₀ mε) _).
  refine (
    match @natη_refl p (mkEl _ _ m₀ mε) in (_ ≡ y) return (P y) with
    | srefl _ =>
    _
    end
  ).
  refine (F _ _).
Defined.

Check (fun p P uO uS => (srefl _ : nat_elim_in p P uO uS Oᶠ ≡ uO)).
Check (fun p P uO uS n => (srefl _ : nat_elim_in p P uO uS (appᶠ Sᶠ n) ≡ uS n (nat_elim_in p P uO uS n))).

Definition nat_elim p
  (P : @El p (Arr natᶠ Typeᶠ))
  (uO : El (appᶠ P Oᶠ))
  (uS : @El p (Prod natᶠ
    (@lamᶠ _ natᶠ Typeᶠ (fun q α n =>
      Arr (@appᶠ _ natᶠ Typeᶠ (α ∗ P) n)
      (@appᶠ _ natᶠ Typeᶠ (α ∗ P) (appᶠ Sᶠ n))))))
  (n : El natᶠ)
:
  El (appᶠ P n).
Proof.
refine (nat_elim_in p (fun n => El (appᶠ P n)) _ _ _).
+ refine uO.
+ let T := type of uS in
  match T with
  | El (Prod ?nat ?f) =>
    unshelve refine (fun n Hn => @appᶠ p (appᶠ P n) (appᶠ P (appᶠ Sᶠ n)) (@dappᶠ p nat f uS n) Hn)
  end.
Defined.

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

Definition falseᶠ {p} : @El p boolᶠ.
Proof.
unshelve refine (mkel _ _ _).
+ refine (fun q α => @false_ q).
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

Definition reflᶠ {p}
  (A : @El p Typeᶠ)
  (x : @El p A) : El (eqᶠ A x x).
Proof.
unshelve refine (mkEl _ _ _ _).
+ intros q α; constructor.
+ intros q α; constructor.
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

Fixpoint lift_nat₀ {p} (n : nat) : @nat_ p :=
match n with
| O => O_
| S n => S_ (fun q α => lift_nat₀ n)
end.

Definition lift_natε {p} (n : nat) :
  ((natᶠ).(el₀) p !).(rel) (fun q α => lift_nat₀ n).
Proof.
induction n; cbn in *.
+ constructor.
+ refine (SR _ IHn).
Defined.

Definition lift_nat {p} (n : nat) : @El p natᶠ.
Proof.
refine (mkel natᶠ (fun q α => lift_nat₀ n) (fun q α => lift_natε _)).
Defined.

Definition proj_nat {p} (n : @El p natᶠ) : nat :=
  nat_elim_in p (fun _ => nat) O (fun _ n => S n) n.

(* Hack not to have to define a nat recursor into SProp *)
Inductive Box (A : SProp) : Type := box : A -> Box A.

Lemma lift_proj_nat :
  forall p n, @lift_nat p (proj_nat n) ≡ n.
Proof.
intros p n.
match goal with [ |- ?P ] => cut (Box P) end.
{ intros [x]; exact x. }
revert n; refine (nat_elim_in _ _ _ _); constructor.
+ reflexivity.
+ destruct X as [[]].
  reflexivity.
Defined.

Definition purify {p} (f : @El p (Arr natᶠ boolᶠ)) (n : nat) : bool :=
match (appᶠ f (lift_nat n)).(el₀) p ! with
| true_ => true
| false_ => false
end.

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

Lemma bool_eta : forall p (x : @El p boolᶠ),
  x ≡ match x.(el₀) p ! with true_ => trueᶠ | false_ => falseᶠ end.
Proof.
intros p [x₀ xε]; unfold El₀, Elε in *; cbn in *.
assert (xr := xε p !).
change (boolR x₀) in xr.
destruct xr; reflexivity.
Qed.

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
  unshelve refine (pairᶠ _ _ (lift_nat n) _).
  move π after Heqθ.
  unfold inf, orb in π.
  destruct Heqθ.
  change (El (eqᶠ boolᶠ (appᶠ f (lift_nat n)) trueᶠ)).
  assert (rw := bool_eta _ (appᶠ f (lift_nat n))).
  apply seq_sym in rw.
  destruct rw.
  unfold purify in π.
  destruct (el₀ (appᶠ f (lift_nat n)) p !).
  - apply reflᶠ.
  - inversion π.
Defined.

(* Lemma sum_eta : forall p A B (s : @El p (sumᶠ A B)),
  s ≡ match s.(el₀) p ! with inl_ _ _ x => inlᶠ A B x | inr_ _ _ y => inrᶠ A B y end.
Proof.
intros p A B [s₀ sε]; unfold El₀, Elε in *; cbn in *.
assert (sr := sε p !).
change (sumR _ _ _ s₀) in sr.
destruct sr; reflexivity.
Qed.
 *)

Lemma isTrue_inf_r : forall p q n, isTrue (q n) -> isTrue ((inf p q) n).
Proof.
intros p q n Hq.
unfold inf.
destruct Hq.
destruct (p n); constructor.
Defined.

Lemma local_to_E {p}
  (f : @El p (Arr natᶠ boolᶠ))
  (e : @El p (sumᶠ E
    (sigᶠ natᶠ
      (@lamᶠ _ natᶠ Typeᶠ (fun q α n => eqᶠ boolᶠ (@appᶠ _ natᶠ boolᶠ (α ∗ f) n) trueᶠ)))))
  : @El p (local f E).
Proof.
destruct (el₀ e p !) as [exn|v]; clear e.
+ apply local_ret, exn.
+ destruct (el₀ v p !) as [n Hn]; clear v.
  change (El (eqᶠ boolᶠ (appᶠ f n) trueᶠ)) in Hn.
  change (@El p natᶠ) in n.
  unshelve refine (mkEl _ _ _ _); [|refine (fun q α r β => sI)].
  refine (fun q α r β => _); cbn.
  exists (proj_nat n); apply β.
  apply isTrue_inf_r.
  clear - Hn.
  unfold purify.
  assert (Hrw := lift_proj_nat _ n).
  apply seq_sym in Hrw; destruct Hrw.
  apply el₀ in Hn.
  specialize (Hn p !).
  cbn in *.
  let T := type of Hn in
  match T with eq_ _ ?X ?Y => assert (Hrw : (X.(el₀) p !) ≡ (Y.(el₀) p !)) end.
  { destruct Hn; reflexivity. }
  clear - Hrw; cbn in *.
  change (el₀ f p ! (! ∗ n) ≡ true_) in Hrw.
  apply seq_sym in Hrw.
  refine (match Hrw in _ ≡ z return isTrue (match z with true_ => true | false_ => false end) with srefl _ => _ end).
  constructor.
Defined.

Lemma local_of_sig {p}
  (P : @El p (Arr natᶠ Typeᶠ))
  (f : @El p (Arr natᶠ boolᶠ))
  (v : @El p (local f (sigᶠ natᶠ P)))
:
  @El p (sigᶠ natᶠ (@lamᶠ _ natᶠ Typeᶠ (fun q α n => @appᶠ q natᶠ Typeᶠ (α ∗ P) n))).
Proof.
Admitted.

End MP.
