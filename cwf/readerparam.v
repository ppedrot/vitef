Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.

Record sig (A : Type) (B : A -> Type) := pair {
  fst : A;
  snd : B fst;
}.

Arguments pair {_ _}.
Arguments fst {_ _}.
Arguments snd {_ _}.

Axiom ℙ : Set.

Definition Ctx@{i} := Type@{i}.

Record Typ@{i j k} (Γ : Ctx@{i}) := {
  typ_elt : forall γ : Γ, (ℙ -> Type@{j});
  typ_rel : forall γ : Γ, (forall p, typ_elt γ p) -> Type@{k};
}.

Arguments typ_elt {_}.
Arguments typ_rel {_}.

Record Trm@{i j k} (Γ : Ctx@{i}) (A : Typ@{i j k} Γ) := {
  trm_elt : forall (γ : Γ) p, A.(typ_elt) γ p;
  trm_rel : forall (γ : Γ), A.(typ_rel) γ (trm_elt γ);
}.

Arguments trm_elt {_ _}.
Arguments trm_rel {_ _}.

Record Sub@{i j} (Γ : Ctx@{i}) (Δ : Ctx@{j}) := {
  sub_sub : Γ -> Δ;
}.

Coercion sub_sub : Sub >-> Funclass.

Definition typ_sub {Γ Δ} (A : Typ Δ) (σ : Sub Γ Δ) : Typ Γ :=
  Build_Typ _ (fun γ p => A.(typ_elt) (σ γ) p) (fun γ => A.(typ_rel) (σ γ)).

Definition trm_sub {Γ Δ} {A : Typ Δ} (t : Trm Δ A) (σ : Sub Γ Δ) : Trm Γ (typ_sub A σ) :=
  Build_Trm Γ (typ_sub A σ) (fun γ p => t.(trm_elt) (σ γ) p) (fun γ => t.(trm_rel) (σ γ)).

Definition idn (Γ : Ctx) : Sub Γ Γ := Build_Sub _ _ (fun γ => γ).

Definition ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve refine (sig Γ (fun γ => sig (forall p, A.(typ_elt) γ p) (A.(typ_rel) γ))).
Defined.

Definition wkn {Γ Δ} (A : Typ Γ) (σ : Sub Γ Δ) : Sub (ext Γ A) Δ.
Proof.
constructor.
refine (fun γ => σ (@fst _ _ γ)).
Defined.

Definition lft {Γ Δ} (A : Typ Δ) (σ : Sub Γ Δ) : Sub (ext Γ (typ_sub A σ)) (ext Δ A).
Proof.
constructor.
unshelve refine (fun γ => pair (σ γ.(fst)) γ.(snd)).
Defined.

Definition rel0 {Γ : Ctx} {A : Typ Γ} : Trm (ext Γ A) (typ_sub A (wkn A (idn _))).
Proof.
unshelve econstructor.
+ refine (fun γ p => γ.(snd).(fst) p).
+ refine (fun γ => γ.(snd).(snd)).
Defined.

Definition cns {Γ Δ} {A : Typ Γ} (σ : Sub Δ Γ) (x : Trm Δ (typ_sub A σ)) : Sub Δ (ext Γ A).
Proof.
unshelve econstructor.
unshelve refine (fun δ => pair (σ δ) (pair (x.(trm_elt) _) (x.(trm_rel) _))).
Defined.

Definition Π {Γ : Ctx} (A : Typ Γ) (B : Typ (ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ p => forall (x : forall p, A.(typ_elt) γ p) (xε : A.(typ_rel) γ x), B.(typ_elt) (pair γ (pair x xε)) p).
+ cbn.
  unshelve refine (fun γ f => forall (x : forall p, A.(typ_elt) γ p) (xε : A.(typ_rel) γ x), B.(typ_rel) _ _).
  - refine (pair γ (pair x xε)).
  - refine (fun p => f p _ _).
Defined.

Definition lam {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm (ext Γ A) B) : Trm Γ (Π A B).
Proof.
unshelve econstructor.
+ refine (fun γ p x xε => t.(trm_elt) _ _).
+ refine (fun γ x xε => t.(trm_rel) _).
Defined.

Definition app {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)) (u : Trm Γ A) :
  Trm Γ (typ_sub B (cns (idn Γ) u)).
Proof.
unshelve econstructor.
+ refine (fun γ p => t.(trm_elt) _ _ _ _).
+ refine (fun γ => t.(trm_rel) _ _ _).
Defined.

Definition Arr {Γ : Ctx} (A B : Typ Γ) := Π A (typ_sub B (wkn _ (idn _))).

Definition Squash {Γ : Ctx} (A : Typ Γ) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ p => A.(typ_elt) γ p).
+ refine (fun γ _ => True).
Defined.

Lemma choice {Γ} {A : Typ Γ} {B : Typ (ext Γ A)} : Trm Γ (Arr (Π A (Squash B)) (Squash (Π A B))).
Proof.
unshelve econstructor; cbn.
+ refine (fun γ p f fε x xε => _).
  apply f.
+ constructor.
Defined.
