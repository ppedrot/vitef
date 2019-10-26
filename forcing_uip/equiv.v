(* Axiom PropExt : forall (A B : Prop), A <-> B -> A = B. *)
Axiom PI : forall (A : Prop) (x y : A), x = y.
Axiom funext : forall A (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g.

Set Primitive Projections.

Axiom ℙ : Type.
Axiom le₀ : ℙ -> ℙ -> Type.

Definition le p q := forall r, le₀ q r -> le₀ p r.

Definition le_id {p} : le p p := fun r k => k.
Definition le_cmp {p q r} (α : le p q) (β : le q r) : le p r := fun r k => α r (β r k).

Notation "p ≤ q" := (le p q) (at level 70, no associativity).
Notation "'!'" := (@le_id _).
Notation "α ∘ β" := (@le_cmp _ _ _ β α) (at level 35).

Record Psh := mkPsh {
  set : ℙ -> Type;
  mon : forall {p q} (α : q ≤ p), set p -> set q;
  mon_id : forall p (x : set p), mon ! x = x;
  mon_cmp : forall p q (α : le q p) r (β : r ≤ q) (x : set p), mon (α ∘ β) x = mon β (mon α x);
}.

Record Nat (A B : Psh) := mkNat {
  hom : forall p, A.(set) p -> B.(set) p;
  nat : forall p q (α : q ≤ p) x,
    hom q (A.(mon) α x) = B.(mon) α (hom p x);
}.

Arguments hom {_ _}.
Arguments nat {_ _}.

Lemma Nat_eq : forall A B (f g : Nat A B),
  (forall p (x : A.(set) p), f.(hom) p x = g.(hom) p x) -> f = g.
Proof.
intros A B [f fn] [g gn] e.
cbn in *.
assert (e' : f = g).
{ apply funext; intros p; apply funext; intros x; apply e. }
destruct e'.
replace fn with gn by apply PI.
reflexivity.
Qed.

Definition Nid {A} : Nat A A.
Proof.
unshelve refine (mkNat _ _ (fun _ x => x) _).
reflexivity.
Defined.

Definition Ncmp {A B C} (f : Nat A B) (g : Nat B C) : Nat A C.
Proof.
unshelve refine (mkNat _ _ (fun p x => g.(hom) p (f.(hom) p x)) _).
intros; rewrite f.(nat), g.(nat); reflexivity.
Defined.

Record Pfc := mkPfc {
  elt : forall p q (α : q ≤ p), Type;
  rel : forall p, (forall q α, elt p q α) -> Prop;
  prm : forall p q (α : q ≤ p), elt p q α = elt q q !;
}.

Definition cast (A : Pfc) {p q} (α : q ≤ p) : A.(elt) q q ! -> A.(elt) p q α :=
  match A.(prm) p q α with eq_refl => fun x => x end.

Record El p (A : Pfc) := mkEl {
  el₀ : forall q (α : q ≤ p), A.(elt) q q !;
  elε : forall q (α : q ≤ p), A.(rel) q (fun r β => cast A β (el₀ r (α ∘ β)));
}.

Arguments el₀ {_ _}.
Arguments elε {_ _}.

Lemma El_eq : forall p A (x y : El p A),
  x.(el₀) = y.(el₀) -> x = y.
Proof.
intros p A [x₀ xε] [y₀ yε] e; cbn in *.
destruct e.
replace yε with xε by apply PI.
reflexivity.
Qed.

Definition lift (A : Pfc) {p q} (α : q ≤ p) (x : El p A) : El q A.
Proof.
unshelve refine (mkEl _ _ (fun r β => x.(el₀) r (α ∘ β)) _).
refine (fun r β => x.(elε) r (α ∘ β)).
Defined.

Record Fnc (A B : Pfc) := mkFnc {
  fnc : forall p (x : El p A), B.(elt) p p !;
  rlz : forall p (x : El p A), B.(rel) p (fun q (α : q ≤ p) => cast B α (fnc q (lift A α x)));
}.

Arguments fnc {_ _}.
Arguments rlz {_ _}.

Lemma Fnc_eq : forall A B (f g : Fnc A B),
  (forall p (x : El p A), f.(fnc) p x = g.(fnc) p x) -> f = g.
Proof.
intros A B [f fn] [g gn] e.
cbn in *.
assert (e' : f = g).
{ apply funext; intros p; apply funext; intros x; apply e. }
destruct e'.
replace fn with gn by apply PI.
reflexivity.
Qed.

Definition App {A B p} (f : Fnc A B) (x : El p A) : El p B.
Proof.
unshelve refine (mkEl _ _ (fun q α => f.(fnc) q (lift A α x)) _).
intros q α.
apply (f.(rlz) q (lift A α x)).
Defined.

Definition Fid {A} : Fnc A A.
Proof.
unshelve refine (mkFnc _ _ (fun p x => x.(el₀) p !) _).
intros p x.
refine (x.(elε) p !).
Defined.

Definition Fcmp {A B C} (f : Fnc A B) (g : Fnc B C) : Fnc A C.
Proof.
unshelve refine (mkFnc _ _ (fun p x => g.(fnc) p (App f x)) _).
intros p x.
refine (g.(rlz) _ (App f x)).
Defined.

Definition F (A : Psh) : Pfc.
Proof.
unshelve refine (
  mkPfc
    (fun p q α => A.(set) q)
    (fun p x => forall q (α : q ≤ p), x q α = A.(mon) α (x p !))
    (fun p q α => eq_refl)).
Defined.

Definition G (A : Pfc) : Psh.
Proof.
unshelve refine (
  mkPsh
    (fun p => El p A)
    (fun p q α x => lift A α x)
    (fun p x => eq_refl)
    (fun p q α r β x => eq_refl)
).
Defined.

Definition Fφ {A B} (f : Nat A B) : Fnc (F A) (F B).
Proof.
unshelve refine (mkFnc _ _ _ _).
+ refine (fun p x => f.(hom) p (x.(el₀) p !)).
+ cbn; intros p x q α.
  rewrite <- f.(nat).
  assert (xε := x.(elε) p ! q α).
  cbn in *.
  rewrite <- xε.
  reflexivity.
Defined.

Lemma Fφ_id : forall A, Fφ (@Nid A) = Fid.
Proof.
intros A.
apply Fnc_eq; intros p α; reflexivity.
Qed.

Lemma Fφ_cmp : forall A B C (f : Nat A B) (g : Nat B C), Fφ (Ncmp f g) = Fcmp (Fφ f) (Fφ g).
Proof.
intros A B C f g.
apply Fnc_eq; intros p α; reflexivity.
Qed.

Definition Gφ {A B} (f : Fnc A B) : Nat (G A) (G B).
Proof.
unshelve refine (mkNat _ _ _ _).
+ refine (fun p x => App f x).
+ cbn; intros p q α x.
  reflexivity.
Defined.

Lemma Gφ_id : forall A, Gφ (@Fid A) = Nid.
Proof.
intros A.
apply Nat_eq; intros p α; reflexivity.
Qed.

Lemma Gφ_cmp : forall A B C (f : Fnc A B) (g : Fnc B C), Gφ (Fcmp f g) = Ncmp (Gφ f) (Gφ g).
Proof.
intros A B C f g.
apply Nat_eq; intros p α; reflexivity.
Qed.

Definition of_GF {A} : Nat (G (F A)) A.
Proof.
unshelve refine (mkNat _ _ _ _).
+ refine (fun p x => x.(el₀) p !).
+ intros p q α [x₀ xε]; cbn in *.
  specialize (xε p ! q α).
  etransitivity; [|apply xε].
  reflexivity.
Defined.

Lemma of_GF_nat : forall A B (f : Nat A B),
  Ncmp of_GF f = Ncmp (Gφ (Fφ f)) of_GF.
Proof.
intros A B f.
apply Nat_eq; intros p x.
reflexivity.
Qed.

Definition to_GF {A} : Nat A (G (F A)).
Proof.
unshelve refine (mkNat _ _ _ _).
+ unshelve refine (fun p x => mkEl _ _ (fun q α => _) _).
  - refine (A.(mon) α x).
  - refine (fun q α r β => A.(mon_cmp) _ _ _ _ _ _).
+ cbn; intros p q α x.
  apply El_eq; cbn.
  apply funext; intros r; apply funext; intros β.
  symmetry; apply A.(mon_cmp).
Defined.

Lemma to_GF_nat : forall A B (f : Nat A B),
  Ncmp f to_GF = Ncmp to_GF (Gφ (Fφ f)).
Proof.
intros A B f.
apply Nat_eq; intros p x; apply El_eq.
apply funext; intros q; apply funext; intros α.
cbn.
rewrite f.(nat); reflexivity.
Qed.

Lemma of_to_GF_id : forall A, Ncmp of_GF to_GF = @Nid (G (F A)).
Proof.
intros A.
apply Nat_eq; intros p x; cbn in *.
apply El_eq; cbn.
apply funext; intros q; apply funext; intros α.
symmetry.
apply x.(elε).
Qed.

Lemma to_of_GF_id : forall A, Ncmp to_GF of_GF = @Nid A.
Proof.
intros A.
apply Nat_eq; intros p x; cbn in *.
apply A.(mon_id).
Qed.

Definition of_FG {A} : Fnc (F (G A)) A.
Proof.
unshelve refine (mkFnc _ _ _ _).
+ refine (fun p x => (x.(el₀) p !).(el₀) p !).
+ intros p [x₀ xε]; cbn in *.
  assert (e : x₀ = (fun q (α : q ≤ p) => lift A α (x₀ p !))).
  { apply funext; intros q; apply funext; intros α.
    apply (xε p ! q α). }
  rewrite e; cbn; clear e.
  apply (x₀ p !).(elε).
Defined.

Lemma of_FG_nat : forall A B (f : Fnc A B),
  Fcmp of_FG f = Fcmp (Fφ (Gφ f)) of_FG.
Proof.
intros A B f.
apply Fnc_eq; intros p [x₀ xε]; cbn in *.
f_equal; apply El_eq; cbn.
apply funext; intros q; apply funext; intros α.
specialize (xε p ! q α).
change (α ∘ !) with (! ∘ α).
rewrite xε.
reflexivity.
Qed.

Definition to_FG {A} : Fnc A (F (G A)).
Proof.
unshelve refine (mkFnc _ _ _ _).
+ refine (fun p x => x).
+ intros p x; cbn; reflexivity.
Defined.

Lemma to_FG_nat : forall A B (f : Fnc A B),
  Fcmp f to_FG = Fcmp to_FG (Fφ (Gφ f)).
Proof.
intros A B f.
apply Fnc_eq; intros p x.
reflexivity.
Qed.

Lemma of_to_FG_id : forall A, Fcmp of_FG to_FG = @Fid (F (G A)).
Proof.
intros A.
apply Fnc_eq; intros p [x₀ xε]; cbn in *.
apply El_eq; cbn.
apply funext; intros q; apply funext; intros α.
change (el₀ (x₀ q (! ∘ α)) q ! = el₀ (x₀ p !) q α).
rewrite (xε p ! q α).
reflexivity.
Qed.

Lemma to_of_FG_id : forall A, Fcmp to_FG of_FG = @Fid A.
Proof.
intros A.
apply Fnc_eq; intros p x; cbn in *.
reflexivity.
Qed.
