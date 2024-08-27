(** This file defines a CwF model of the Dialectica transformation.

Dialectica is a famous logical interpretation of intuitionistic arithmetic
due to Gödel. In modern terms, it can be seen as a realizability
interpretation: proofs [p : A] are interpreted as programs {p} satisfying
a predicate {A} obtained systematically from the formula A.

Compared with the more standard Kreisel realizability which is basically what
we call today "erasure", Dialectica endows proofs of [A → B] with more
data than just a function from [A] to [B]. Namely, it also gives
information about how this function uses its argument. This corresponds
computationally to the ability to track the stacks against which variables
are dereferenced. See my PhD "A Materialist Dialectica" for more detail on
the topic.

The original presentation of Dialectica is problematic from a computational point
of view as it does not preserve the equational theory of the original logic seen
as a fancy λ-calculus. From a Curry-Howard point of view, this is VERY BAD (TM).
Thankfully, some variants are better behaved. This is the case of the Diller-Nahm
variant whose introduction was motivated by totally different reasons, namely
the requirement of decidability of orthogonality in the original Dialectica.

We show in this file that assuming some abstract notion of multiset, i.e. a
monad equipped with a commutative monoid structure compatible with the monadic
operations, a.k.a. a "semi-ringoid", one can define a Dialectica model of
dependent types. This precise construction was never really published, although
there are hints of this in my PhD and in a TYPES'17 abstract coauther with Andrej
Bauer. There was even a companion handwritten draft that somehow ended up on the
internet via some Google Drive, but its precise location has long been lost
to the mist of time.

This construction can be seen as a simplification of the Moss-von Glehn
Diller-Nahm model described in their paper

"Dialectica models of type theory" (https://arxiv.org/abs/2105.00283).

Trigger warning: the above paper is way too categorical to my taste
and I have constructive evidence that some other people got their brain
clogged by the high-fibration content found in there. This very file
should hopefully make it easy to grasp what is really going on there
for mere mortals that were not sprung out of Grothendieck's thigh.

For readability, we follow the category with families (CwF) presentation
of type theory. This is still a bit too category-friendly to my taste,
but despited the name CwFs are rather fine even from a type-theoretical
point of view. (I suspect the name is just to lure category theorists
into type theory, most of the CwF stuff is pretty a-categorical.)

CwF allow stratifying the definitions of objects in contexts
Γ, Δ : Ctx, substitutions between contexts σ, τ : Sub Γ Δ,
types in a context A B : Typ Γ and terms Trm Γ A. Substitutions
act on these objects in the expected way and we get a bunch of type
and term formers together with equations.

The Dialectica CwF construction given here uses the ambient type theory as
a target CwF, as this makes a lot of stuff definitional, which means less
coherence hell. In theory we could abstract this away and get a more general
transformation which would form a syntactic Dialectica model of MLTT, assuming
some magic in the target theory.

*)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** For simplicity, we turn Coq into a degraded topos, assuming funext and blurring
  the lines between Prop and SProp. *)

Inductive Box@{i} (A : Type@{i}) : SProp := box : A -> Box A.

Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
Axiom pirrel : forall (A : Prop) (x y : A), x = y.
Axiom unbox : forall (A : Prop), Box A -> A.

Set Primitive Projections.

Record sig (A : Type) (B : A -> Type) := pair {
  fst : A;
  snd : B fst;
}.

Arguments pair {_ _}.
Arguments fst {_ _}.
Arguments snd {_ _}.

Lemma sig_eq_intro : forall (A : Type) (B : A -> Type) (p q : sig A B) (e : fst p = fst q),
  eq_rect _ B (snd p) _ e = snd q -> p = q.
Proof.
intros.
destruct p as [x y], q as [x' y']; cbn in *.
destruct e; f_equal; assumption.
Qed.

Definition prod (A B : Type) := sig A (fun _ => B).

Lemma prod_eq_intro : forall (A : Type) (B : Type) (p q : prod A B),
  fst p = fst q -> snd p = snd q -> p = q.
Proof.
intros * e1 e2.
destruct p as [x y], q as [x' y']; cbn in *.
now destruct e1, e2.
Qed.

(** We axiomatize our abstract multiset structure. It is a monad. *)

Axiom M@{i} : Type@{i} -> Type@{i}.
Axiom ret : forall {A : Type}, A -> M A.
Axiom bind : forall {A B : Type}, M A -> (A -> M B) -> M B.

Axiom bind_ret_l : forall A B (x : A) (f : A -> M B), bind (ret x) f = f x.
Axiom bind_ret_r : forall A (α : M A), bind α ret = α.
Axiom bind_assoc : forall A B C (α : M A) f g,
  @bind B C (@bind A B α f) g = bind α (fun x => bind (f x) g).

(** The abstract multiset is furthermore a commutative monoid. *)

Axiom nul : forall A, M A.
Axiom add : forall {A}, M A -> M A -> M A.

Axiom add_id_l : forall A (α : M A), add (nul A) α = α.
Axiom add_id_r : forall A (α : M A), add α (nul A) = α.
Axiom add_assoc : forall A (α₁ α₂ α₃ : M A), add α₁ (add α₂ α₃) = add (add α₁ α₂) α₃.
Axiom add_comm : forall A (α₁ α₂ : M A), add α₁ α₂ = add α₂ α₁.

(** The commutative monoid operations distribute over the monad operations. *)

Axiom bind_nul : forall A B (f : A -> M B), bind (nul A) f = nul B.
Axiom bind_add : forall A B (α₁ α₂ : M A) (f : A -> M B), bind (add α₁ α₂) f = add (bind α₁ f) (bind α₂ f).

Axiom bind_nul_rev : forall A B (α : M A), bind α (fun _ => nul B) = nul B.
Axiom bind_add_rev : forall A B (α : M A) (f g : A -> M B), bind α (fun x => add (f x) (g x)) = add (bind α f) (bind α g).

(** Derived operations and lemmas. *)

Definition map {A B} (f : A -> B) (α : M A) : M B := bind α (fun x => ret (f x)).

Lemma map_ret : forall A B (f : A -> B) (x : A), map f (ret x) = ret (f x).
Proof.
intros; unfold map.
now rewrite bind_ret_l.
Qed.

Lemma map_map : forall A B C (f : A -> B) (g : B -> C) (α : M A),
  map g (map f α) = map (fun x => g (f x)) α.
Proof.
intros; unfold map.
rewrite bind_assoc; f_equal.
apply funext; intros x; now rewrite bind_ret_l.
Qed.

Lemma map_bind : forall A B C (f : A -> M B) (g : B -> C) (α : M A),
  map g (bind α f) = bind α (fun x => map g (f x)).
Proof.
intros; unfold map.
now rewrite bind_assoc.
Qed.

Lemma map_nul : forall A B (f : A -> B), map f (nul _) = (nul _).
Proof.
intros; apply bind_nul.
Qed.

Lemma map_add : forall A B (f : A -> B) (α₁ α₂ : M A), map f (add α₁ α₂) = add (map f α₁) (map f α₂).
Proof.
intros; apply bind_add.
Qed.

(** We define algebras for our abstract multiset:
    basically a monad algebra compatible with the monoidal structure. *)

Record isAlg (A : Type) (hA : M A -> A) (nulA : A) (addA : A -> A -> A) := {
  alg_ret : forall x, hA (ret x) = x;
  alg_bnd : forall (x : M (M A)), hA (map hA x) = hA (bind x (fun x => x));
  alg_run_nul : hA (nul _) = nulA;
  alg_run_add : forall x y, hA (add x y) = addA (hA x) (hA y);
}.

Class Alg@{i} (A : Type@{i}) := {
  alg_fun : M A -> A;
  alg_nul : A;
  alg_add : A -> A -> A;
  alg_spc : Box (isAlg A alg_fun alg_nul alg_add);
}.

Arguments alg_fun {A _}.
Arguments alg_nul {A _}.
Arguments alg_add {A _}.

Notation "'ε'" := (@alg_fun _ _).
Notation "∅" := (@alg_nul _ _).
Notation "x ⊕ y" := (@alg_add _ _ x y) (at level 35).

(** A bunch of helper lemmas. *)

Lemma Alg_ret : forall {A} {algA : Alg A} (x : A), ε (ret x) = x.
Proof.
intros; eapply alg_ret, unbox, algA.
Qed.

Lemma Alg_bind₀ : forall {A} {algA : Alg A} (α : M (M A)), ε (map ε α) = ε (bind α (fun x => x)).
Proof.
intros; eapply alg_bnd, unbox, algA.
Qed.

Lemma Alg_bind : forall {A B} {algB : Alg B} (α : M A) (f : A -> M B),
  ε (bind α f) = ε (bind α (fun x => ret (ε (f x)))).
Proof.
intros.
transitivity (ε (bind (map f α) (fun x => x))).
{ unfold map; rewrite bind_assoc; do 2 f_equal.
  apply funext; intros x; now rewrite bind_ret_l. }
rewrite <- Alg_bind₀; f_equal.
now rewrite map_map.
Qed.

Lemma Alg_run_nul : forall {A} {algA : Alg A}, ε (nul _) = ∅.
Proof.
intros; eapply alg_run_nul, unbox, algA.
Qed.

Lemma Alg_run_add : forall {A} {algA : Alg A} (α₁ α₂ : M A), ε (add α₁ α₂) = (ε α₁) ⊕ (ε α₂).
Proof.
intros; eapply alg_run_add, unbox, algA.
Qed.

Lemma Alg_id_l : forall {A} {algA : Alg A} (x : A), ∅ ⊕ x = x.
Proof.
intros.
rewrite <- (Alg_ret x), <- Alg_run_nul, <- Alg_run_add.
now rewrite add_id_l.
Qed.

Lemma Alg_id_r : forall {A} {algA : Alg A} (x : A), x ⊕ ∅ = x.
Proof.
intros.
rewrite <- (Alg_ret x), <- Alg_run_nul, <- Alg_run_add.
now rewrite add_id_r.
Qed.

Lemma Alg_assoc : forall {A} {algA : Alg A} (x y z : A), x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z.
Proof.
intros.
rewrite <- (Alg_ret x), <- (Alg_ret y), <- (Alg_ret z), <- !Alg_run_add.
now rewrite add_assoc.
Qed.

Lemma Alg_comm : forall {A} {algA : Alg A} (x y : A), x ⊕ y = y ⊕ x.
Proof.
intros.
rewrite <- (Alg_ret x), <- (Alg_ret y), <- !Alg_run_add.
now rewrite add_comm.
Qed.

(** Important algebra formers *)

Instance Alg_M {A} : Alg (M A).
Proof.
unshelve econstructor.
+ refine (fun α => bind α (fun x => x)).
+ refine (nul _).
+ refine (add).
+ do 2 constructor.
  - intros α; now rewrite bind_ret_l.
  - intros α; unfold map.
    rewrite !bind_assoc; f_equal; apply funext; intros β.
    now rewrite bind_ret_l.
  - now rewrite bind_nul.
  - intros; now rewrite bind_add.
Defined.

Instance Alg_unit : Alg unit.
Proof.
unshelve econstructor.
+ refine (fun α => tt).
+ refine (tt).
+ refine (fun p q => tt).
+ do 2 constructor; try reflexivity.
  intros []; reflexivity.
Defined.

Instance Alg_prod {A B} : Alg A -> Alg B -> Alg (prod A B).
Proof.
intros hA hB.
unshelve econstructor.
+ refine (fun α => pair (hA.(alg_fun) (map fst α)) (hB.(alg_fun) (map (@snd _ (fun _ => B)) α))).
+ refine (pair ∅ ∅).
+ refine (fun p q => pair (p.(fst) ⊕ q.(fst)) (p.(snd) ⊕ q.(snd))).
+ do 2 constructor.
  - intros [x y]; cbn; f_equal; now rewrite map_ret, Alg_ret.
  - intros α; f_equal; rewrite map_map; cbn;
    rewrite <- map_map with (g := ε), Alg_bind₀;
    f_equal; unfold map; rewrite !bind_assoc; f_equal;
    apply funext; intros β; now rewrite bind_ret_l.
  - f_equal; now rewrite map_nul, Alg_run_nul.
  - intros; f_equal; cbn; now rewrite map_add, Alg_run_add.
Defined.

(** Let-binding for algebras. Give me my CBPV model already! *)

Definition Mlet {A B} {algB : Alg B} (α : M A) (f : A -> B) : B := ε (map f α).

Lemma Mlet_ret : forall {A B} {algB : Alg B} (x : A) (f : A -> B), Mlet (ret x) f = f x.
Proof.
intros; unfold Mlet, map.
now rewrite bind_ret_l, Alg_ret.
Qed.

Lemma Mlet_assoc : forall {A B C} {algC : Alg C} (α : M A) (f : A -> M B) (g : B -> C),
  Mlet (bind α f) g = Mlet α (fun x => Mlet (f x) g).
Proof.
intros; unfold Mlet; cbn.
rewrite <- map_map with (g := ε).
rewrite Alg_bind₀.
f_equal.
rewrite map_bind; unfold map.
rewrite !bind_assoc.
f_equal.
apply funext; intros x.
now rewrite !bind_ret_l.
Qed.

Lemma Mlet_map : forall {A B C} {algC : Alg C} (α : M A) (f : A -> B) (g : B -> C),
  (Mlet (map f α) g) = Mlet α (fun x => g (f x)).
Proof.
intros; unfold Mlet.
now rewrite map_map.
Qed.

Lemma Mlet_nul : forall {A B} {algB : Alg B} (α : M A), Mlet α (fun x => ∅) = @alg_nul B algB.
Proof.
intros; unfold Mlet, map.
set (e := ∅) at 1; rewrite <- Alg_run_nul; unfold e; clear e.
rewrite <- bind_nul_rev with (α := α).
symmetry; rewrite Alg_bind; do 2 f_equal.
apply funext; intros x.
now rewrite Alg_run_nul.
Qed.

Lemma Mlet_add : forall {A B} {algB : Alg B} (α : M A) (f g : A -> B),
  Mlet α (fun x => (f x) ⊕ (g x)) = (Mlet α f) ⊕ (Mlet α g).
Proof.
intros; symmetry; unfold Mlet.
rewrite <- Alg_run_add.
unfold map. rewrite <- bind_add_rev, Alg_bind; do 2 f_equal.
apply funext; intros x.
now rewrite Alg_run_add, !Alg_ret.
Qed.

(** The Dialectica CwF proper *)

(** A type A in the simply-typed Dialectica is interpreted as:
  - a witness type W(A) : Type
  - a counter type C(A) : W(A) → Type.

  Since contexts are just glorified simple types, they have a similar
  structure. Note that we request the counter types of contexts to be
  M-algebras, which we do not for normal types. The reason is that we will
  get the algebra structure for free in context extension. Basically,
  this is a manifestation of a CBPV adjunction in call-by-name. *)

Record Ctx@{i} := {
  ctx_wit : Type@{i};
  ctx_ctr : forall (γ : ctx_wit), Type@{i};
  ctx_alg :: forall (γ : ctx_wit), Alg (ctx_ctr γ);
}.

Record isSub {Γ Δ : Ctx}
  (fwd : forall (γ : ctx_wit Γ), ctx_wit Δ)
  (bwd : forall (γ : ctx_wit Γ), ctx_ctr Δ (fwd γ) -> ctx_ctr Γ γ) := {
  sub_alg : forall γ π, bwd γ (ε π) = ε (map (bwd γ) π);
}.

(** Morphisms between contexts W(Γ), C(Γ) and W(Δ), C(Δ) are made of:
  - a forward substitution σ⁺ : W(Γ) → W(Δ)
  - a backward substitution σ⁻ : forall (γ : W(Γ)), C(Δ)[σ(γ)] → C(Γ)[γ]

  Note that σ⁻ goes the other way around: this two-way interpretation of morphisms
  is the special signature of Dialectica.

  We further mandate that backward substitutions are algebra morphisms for good
  measure. This is once again textbook (dependent) CBPV.

  As a general principle, W and forward components will be basically the underlying
  equivalent structure from the target CwF (except for functions). The interesting
  stuff you should be looking at are C types and backward components.

*)

Record Sub (Γ Δ : Ctx) := {
  sub_fwd : forall (γ : ctx_wit Γ), ctx_wit Δ;
  sub_bwd : forall (γ : ctx_wit Γ), ctx_ctr Δ (sub_fwd γ) -> ctx_ctr Γ γ;
  sub_spc : Box (isSub sub_fwd sub_bwd);
}.

Arguments sub_fwd {Γ Δ}.
Arguments sub_bwd {Γ Δ}.

Lemma Sub_alg : forall {Γ Δ} (σ : Sub Γ Δ) (γ : ctx_wit Γ) π, sub_bwd σ γ (ε π) = ε (map (sub_bwd σ γ) π).
Proof.
intros; apply sub_alg, unbox, σ.
Qed.

Lemma Sub_nul : forall {Γ Δ} (σ : Sub Γ Δ) (γ : ctx_wit Γ), sub_bwd σ γ ∅ = ∅.
Proof.
intros.
now rewrite <- Alg_run_nul, Sub_alg, !map_nul, Alg_run_nul.
Qed.

Lemma Sub_add : forall {Γ Δ} (σ : Sub Γ Δ) (γ : ctx_wit Γ) π₁ π₂, sub_bwd σ γ (π₁ ⊕ π₂) = sub_bwd σ γ π₁ ⊕ sub_bwd σ γ π₂.
Proof.
intros.
rewrite <- (Alg_ret π₁), <- (Alg_ret π₂).
rewrite <- Alg_run_add, Sub_alg, !map_add, !map_ret.
now rewrite Alg_run_add, !Alg_ret.
Qed.

(** Basic substitution formers: Sub is a category. [HE SAID THE WORD!] *)

Definition idn (Γ : Ctx) : Sub Γ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ => γ).
+ refine (fun γ π => π).
+ do 2 constructor.
  intros; unfold map; now rewrite bind_ret_r.
Defined.

Definition cmp {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Ξ) : Sub Γ Ξ.
Proof.
unshelve econstructor.
+ refine (fun γ => τ.(sub_fwd) (σ.(sub_fwd) γ)).
+ refine (fun γ π => σ.(sub_bwd) γ (τ.(sub_bwd) _ π)).
+ do 2 constructor.
  intros; now rewrite !Sub_alg, map_map.
Defined.

(** We now define (dependent) types. They're just like contexts,
    except that we will get the M-algebra structure sneakily out
    of context extension. The reason is that in CBPV, call-by-name
    types are interpreted as computation types, and we interpret
    [Γ, A] as [Γ], U [A]. The U functor is here the free M-algebra
    functor. *)

Record Typ@{i j k} (Γ : Ctx@{i}) := {
  typ_wit : forall (γ : Γ.(ctx_wit)), Type@{j};
  typ_ctr : forall (γ : Γ.(ctx_wit)) (x : typ_wit γ), Type@{k};
}.

Arguments typ_wit {Γ}.
Arguments typ_ctr {Γ}.

Definition typ_sub {Γ Δ : Ctx} (A : Typ Γ) (σ : Sub Δ Γ) : Typ Δ.
Proof.
unshelve econstructor.
+ refine (fun γ => A.(typ_wit) (σ.(sub_fwd) γ)).
+ refine (fun γ x => A.(typ_ctr) (σ.(sub_fwd) γ) x).
Defined.

Lemma typ_sub_idn : forall Γ A, typ_sub A (idn Γ) = A.
Proof.
reflexivity.
Defined.

Lemma typ_sub_cmp : forall Γ Δ Ξ A σ τ, typ_sub A (@cmp Γ Δ Ξ σ τ) = typ_sub (typ_sub A τ) σ.
Proof.
reflexivity.
Defined.

(** We define terms. Just like substitutions, there are two
    parts to a term: a forward morphism and a backward morphism.
    The second one depends on the first one. Once again due to
    CBPV being hidden behind the curtains, we do not need the fact that
    the backward morphism is an algebra morphism. It wouldn't make
    sense anyway as the type is not even an algebra. This will appear
    for free at some later point. *)

Record Trm (Γ : Ctx) (A : Typ Γ) := {
  trm_fwd : forall (γ : Γ.(ctx_wit)), typ_wit A γ;
  trm_bwd : forall (γ : Γ.(ctx_wit)), typ_ctr A γ (trm_fwd γ) -> ctx_ctr Γ γ;
}.

Arguments trm_fwd {_ _}.
Arguments trm_bwd {_ _}.

(* A helper function *)

Lemma trm_eq_intro : forall Γ A (t u : Trm Γ A) (e : forall γ, t.(trm_fwd) γ = u.(trm_fwd) γ),
  (forall γ π, t.(trm_bwd) γ π = u.(trm_bwd) γ (eq_rect _ (typ_ctr A γ) π _ (e γ))) ->
  t = u.
Proof.
intros.
destruct t as [tf tb], u as [uf ub]; cbn in *.
assert (e₀ := funext _ _ _ _ e); destruct e₀; f_equal.
apply funext; intros γ; apply funext; intros π.
specialize (H γ π).
replace (e γ) with (@eq_refl _ (tf γ)) in H by apply pirrel.
apply H.
Qed.

Definition trm_sub {Γ Δ : Ctx} {A : Typ Γ} (x : Trm Γ A) (σ : Sub Δ Γ) : Trm Δ (typ_sub A σ).
Proof.
unshelve econstructor.
+ refine (fun γ => x.(trm_fwd) _).
+ refine (fun γ π => σ.(sub_bwd) _ (x.(trm_bwd) _ π)).
Defined.

Lemma trm_sub_idn : forall Γ (A : Typ Γ) (x : Trm Γ A), trm_sub x (idn Γ) = x.
Proof.
reflexivity.
Qed.

Lemma trm_sub_cmp : forall Γ Δ Ξ (A : Typ Ξ) (x : Trm Ξ A) (σ : Sub Γ Δ) (τ : Sub Δ Ξ),
  trm_sub x (cmp σ τ) = trm_sub (trm_sub x τ) σ.
Proof.
reflexivity.
Qed.

(** We now have all the necessary infrastructure. The rest of the file is dedicated
    to the definition of various formers for contexts, types and terms. *)

(** The empty context. *)

Definition eps : Ctx.
Proof.
unshelve econstructor.
+ refine unit.
+ refine (fun _ => unit).
+ intros; apply Alg_unit.
Defined.

Definition drp (Γ : Ctx) : Sub Γ eps.
Proof.
unshelve econstructor.
+ refine (fun γ => tt).
+ refine (fun γ π => ∅).
+ do 2 constructor.
  cbn; intros γ π.
  symmetry; apply Mlet_nul.
Defined.

Lemma drp_eta : forall Γ (σ : Sub Γ eps), σ = drp Γ.
Proof.
intros Γ [σf σb σa]; unfold drp.
assert (e : (fun _ => tt) = σf); [|destruct e].
{ apply funext; intros; now destruct σf. }
assert (e : (fun γ π => ∅) = σb); [|destruct e].
{ apply funext; intros γ; apply funext; intros [].
  apply unbox in σa; destruct σa as [σa]; cbn in *.
  symmetry; etransitivity; [apply (σa γ (nul _))|].
  unfold map; now rewrite bind_nul, Alg_run_nul. }
reflexivity.
Qed.

(** Context extension. W(Γ, A) is W(Γ), W(A) and
    C(Γ, A)[γ, x] is just C(Γ)[γ] × M (C(A)[x]). Note the M. *)

Definition ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve econstructor.
+ refine (sig Γ.(ctx_wit) (fun γ => A.(typ_wit) γ)).
+ refine (fun γ => prod (Γ.(ctx_ctr) γ.(fst)) (M (A.(typ_ctr) γ.(fst) γ.(snd)))).
+ cbn; intros γ.
  apply Alg_prod.
  - apply ctx_alg.
  - apply Alg_M.
Defined.

(** Weakening. As mentioned before, this is just weakening on the
    forward component. On the backward component, we need to pull
    a proof W(Γ), x : W(A) ⊢ M (C(A)[x]) out of thin air. Just pick
    the empty set. This makes the function algebraic. *)

Definition wkn {Γ Δ} (A : Typ Γ) (σ : Sub Γ Δ) : Sub (ext Γ A) Δ.
Proof.
unshelve econstructor.
+ refine (fun γ => σ.(sub_fwd) (γ.(fst))).
+ refine (fun γ π => pair (σ.(sub_bwd) _ π) ∅).
+ do 2 constructor.
  intros [γ x] π; cbn.
  rewrite !Sub_alg, !map_map; cbn; f_equal.
  unfold map; rewrite bind_assoc; cbn.
  symmetry; etransitivity; [|apply bind_nul_rev with (α := π)].
  f_equal; apply funext; intros ρ.
  now rewrite bind_ret_l.
Defined.

Lemma wkn_cmp : forall Γ Δ Ξ A (σ : Sub Γ Δ) (τ : Sub Δ Ξ),
  wkn A (cmp σ τ) = cmp (wkn A σ) τ.
Proof.
reflexivity.
Qed.

(** Lifting. Again, just lifting on the forward component.
    On the backward component we must provide an algebraic proof
    of W(Γ), x : W(A) ⊢ M (C(A)[x]) → M (C(A)[x]). That will be
    the identity. *)

Lemma lft {Γ Δ} (A : Typ Δ) (σ : Sub Γ Δ) : Sub (ext Γ (typ_sub A σ)) (ext Δ A).
Proof.
unshelve econstructor.
+ refine (fun γ => pair (sub_fwd σ γ.(fst)) γ.(snd)).
+ refine (fun γ π => pair (sub_bwd σ γ.(fst) π.(fst)) π.(snd)).
+ do 2 constructor.
  intros [γ x] π; cbn.
  rewrite !Sub_alg, !map_map; reflexivity.
Defined.

(** The one variable, to bring them all and in the darkness bind them.
    Forward component is again standard. For the backward one, this is
    the dual situation to weakening, we must now come up with a proof
    of C(Γ)[γ] but nothing in sight. The empty one will do. *)

Definition rel0 {Γ : Ctx} {A : Typ Γ} : Trm (ext Γ A) (typ_sub A (wkn A (idn _))).
Proof.
unshelve econstructor.
+ refine (fun γ => γ.(snd)).
+ refine (fun γ π => pair ∅ (ret π)).
Defined.

(** Extension of a substitution. Forward component is standard.
    Now we get to see something really interesting in the backward component.
    We have to produce a C(Δ) but there are two potential ways to get one:
    one coming from the backward term, one from the backward substitution.
    If we pick only one arbitrarily, we'll break the equational theory of this
    former. Fair enough, we can just sum them up as C(Γ) is a monoid. *)

Definition cns {Γ Δ} {A : Typ Γ} (σ : Sub Δ Γ) (x : Trm Δ (typ_sub A σ)) : Sub Δ (ext Γ A).
Proof.
unshelve econstructor.
+ refine (fun δ => pair (σ.(sub_fwd) δ) (x.(trm_fwd) δ)).
+ cbn; refine (fun δ π => _).
  refine ((σ.(sub_bwd) _ π.(fst)) ⊕ (Mlet π.(snd) (fun ρ => x.(trm_bwd) δ ρ))).
+ do 2 constructor; intros δ π; cbn.
  match goal with [ |- _ = ε (map ?h π) ] => change (ε (map h π)) with (Mlet π h) end.
  rewrite Sub_alg.
  match goal with [ |- ε (map ?h ?π) ⊕ _ = _ ] => change (ε (map h π)) with (Mlet π h) end.
  rewrite Mlet_assoc, !Mlet_map, Mlet_add; reflexivity.
Defined.

Lemma cns_rel0 : forall Γ Δ A (σ : Sub Δ Γ) x, trm_sub (@rel0 _ A) (cns σ x) = x.
Proof.
intros Γ Δ A σ [xf xb].
unfold trm_sub; f_equal.
apply funext; intros δ; apply funext; intros π; cbn.
now rewrite Sub_nul, Alg_id_l, Mlet_ret.
Qed.

(** Product type and term formers *)

(** This is LE Dialectica type former. Rather than just a function,
    the witness type packs up some information about the use of variables in
    the forward function. Namely,

    W(Π (x : A). B) := Π(x : W(A)). Σ(y : W(B)). C(B)[y] → M (C(A)[x])

    Note the parasitic reverse component C(B)[y] → M (C(A)[x]), the quintessence
    of Dialectica-ness.

    For the counter type, this is just your favourite KAM stack former
    with dependent noise.

    C(Π(x : A). B)[f] := Σ(x : W(A)). C(B)[fst (f x)]

 *)

Definition Π {Γ : Ctx} (A : Typ Γ) (B : Typ (ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor.
+ unshelve refine (fun γ =>
    forall (x : typ_wit A γ),
      sig (typ_wit B (pair γ x)) (fun y => typ_ctr B (pair γ x) y -> M (typ_ctr A γ x))
  ).
+ unshelve refine (fun γ f =>
    sig (typ_wit A γ) (fun x => typ_ctr B (pair γ x) (f x).(fst))
  ).
Defined.

(** Lambda-abstraction. As a good call-by-name λ, this is basically
    an isomorphism known by the wisest experts as curryfication. *)

Definition lam {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm (ext Γ A) B) : Trm Γ (Π A B).
Proof.
unshelve econstructor.
+ unshelve refine (fun γ x => pair _ _).
  - refine (t.(trm_fwd) (pair γ x)).
  - refine (fun π => (t.(trm_bwd) (pair γ x) π).(snd)).
+ refine (fun γ π => (t.(trm_bwd) (pair γ π.(fst)) π.(snd)).(fst)).
Defined.

(** Application. Same phenomenon as for [cns], there are two ways a variable
    can be used in [t u]. Either it is used directly in [t] or it is used in
    [u] through the uses of the argument in [t]. We must merge these two paths. *)

Definition app {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)) (u : Trm Γ A) :
  Trm Γ (typ_sub B (cns (idn Γ) u)).
Proof.
unshelve econstructor.
+ refine (fun γ => (t.(trm_fwd) γ (u.(trm_fwd) γ)).(fst)).
+ refine (fun γ π => _ ⊕ _).
  - refine (t.(trm_bwd) γ (pair (u.(trm_fwd) γ) π)).
  - refine (Mlet ((t.(trm_fwd) γ (u.(trm_fwd) γ)).(snd) π) (u.(trm_bwd) γ)).
Defined.

Lemma Π_sub : forall {Γ Δ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (σ : Sub Δ Γ),
  typ_sub (Π A B) σ = Π (typ_sub A σ) (typ_sub B (lft A σ)).
Proof.
reflexivity.
Qed.

Lemma lam_sub : forall {Γ Δ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm (ext Γ A) B) (σ : Sub Δ Γ),
  trm_sub (lam t) σ = lam (trm_sub t (lft _ σ)).
Proof.
reflexivity.
Qed.

Lemma app_sub : forall {Γ Δ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)}
  (t : Trm Γ (Π A B)) (u : Trm Γ A) (σ : Sub Δ Γ),
  trm_sub (app t u) σ = @app _ (typ_sub A σ) (typ_sub B (lft A σ)) (trm_sub t σ) (trm_sub u σ).
Proof.
intros; unfold trm_sub, app; cbn; f_equal.
apply funext; intros γ; apply funext; intros π; cbn.
rewrite Sub_add; f_equal.
unfold Mlet; rewrite Sub_alg, !map_map.
reflexivity.
Qed.

(** The β rule is miraculously strict. *)

Lemma lam_app_beta : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)}
  (t : Trm (ext Γ A) B) (u : Trm Γ A), app (lam t) u = trm_sub t (cns (idn Γ) u).
Proof.
reflexivity.
Qed.

(* Some like it HoTT... *)
Lemma trm_Π_eq_intro : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t u : Trm Γ (Π A B))
  (ef : forall γ x, (t.(trm_fwd) γ x).(fst) = (u.(trm_fwd) γ x).(fst)),
  (forall γ x π, (t.(trm_fwd) γ x).(snd) π = (u.(trm_fwd) γ x).(snd) (eq_rect _ _ π _ (ef γ x))) ->
  (forall γ x π, t.(trm_bwd) γ (pair x π) = u.(trm_bwd) γ (pair x (eq_rect _ (typ_ctr B (pair γ x)) π _ (ef γ x)))) ->
  t = u.
Proof.
intros * eb er.
destruct t as [tf tb], u as [uf ub].
pose (tff := fun γ x => (tf γ x).(fst)).
pose (tfb := fun γ x => (tf γ x).(snd)).
change tf with (fun γ x => pair (tff γ x) (tfb γ x)) in tb, ef, eb, er |- *.
clearbody tfb.
change (forall γ x, typ_ctr B {| fst := γ; snd := x |} (tff γ x) -> M (typ_ctr A γ x)) in tfb.
clearbody tff; clear tf.
pose (uff := fun γ x => (uf γ x).(fst)).
pose (ufb := fun γ x => (uf γ x).(snd)).
change uf with (fun γ x => pair (uff γ x) (ufb γ x)) in ub, ef, eb, er |- *.
clearbody ufb.
change (forall γ x, typ_ctr B {| fst := γ; snd := x |} (uff γ x) -> M (typ_ctr A γ x)) in ufb.
clearbody uff; clear uf.
cbn in *.
unshelve eapply trm_eq_intro.
+ cbn; intros γ.
  assert (e : tff = uff).
  { abstract (do 2 (apply funext; intro); apply ef). }
  destruct e.
  assert (e : tfb = ufb).
  { clear - eb. apply funext; intros γ; apply funext; intros x; apply funext; intros π.
    specialize (eb γ x π).
    rewrite eb; f_equal.
    replace (ef γ x) with (@eq_refl _ (tff γ x)) by apply pirrel.
    reflexivity. }
  now destruct e.
+ cbn; intros γ [x π]; cbn in *.
  match goal with [ |- context [ eq_rect ?A ?P ?u ?y ?p ] ] => set (e := p); clearbody e end.
  etransitivity; [apply er|].
  f_equal.
  unshelve eapply sig_eq_intro; cbn.
  - destruct e; reflexivity.
  - cbn.
    assert (eff : tff = uff).
    { do 2 (apply funext; intro); apply ef. }
    destruct eff; cbn.
    assert (efb : tfb = ufb).
    { clear - eb. apply funext; intros γ; apply funext; intros x; apply funext; intros π.
      specialize (eb γ x π).
      rewrite eb; f_equal.
      replace (ef γ x) with (@eq_refl _ (tff γ x)) by apply pirrel.
      reflexivity. }
    destruct efb.
    repeat match goal with [ |- context [ eq_rect ?A ?P ?u ?y ?p ] ] =>
      set (e' := p); clearbody e'; assert (H : e' = eq_refl) by apply pirrel; rewrite H; clear e' H; cbn
    end.
    reflexivity.
Qed.

(** The η rule *)

Lemma lam_eta : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)),
  lam (@app (ext Γ A) (typ_sub A (wkn _ (idn _))) (typ_sub B (lft A _)) (trm_sub t (wkn A (idn Γ))) rel0) = t.
Proof.
intros.
unshelve eapply trm_Π_eq_intro.
+ reflexivity.
+ cbn; intros γ x π.
  rewrite add_id_l; rewrite map_map; unfold map; rewrite bind_assoc.
  etransitivity; [|apply bind_ret_r].
  f_equal; apply funext; intros ρ.
  now rewrite bind_ret_l.
+ cbn; intros γ x π.
  rewrite map_map; cbn.
  match goal with [ |- _ ⊕ (ε (map ?f ?t)) = _ ] => change (ε (map ?f ?t)) with (Mlet t f) end.
  now rewrite Mlet_nul, Alg_id_r.
Qed.

(** Sum type and term formers *)

(** Nothing to see here.

    W(A + B) := W(A) + W(B)
    C(A + B)[inl x] := C(A)[x]
    C(A + B)[inr y] := C(B)[y]

    The intuitionistic content is preserved. In particular we inherit canonicity.

*)

Definition Sum {Γ : Ctx} (A B : Typ Γ) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ => A.(typ_wit) γ + B.(typ_wit) γ)%type.
+ refine (fun γ s => match s with inl x => A.(typ_ctr) γ x | inr y => B.(typ_ctr) γ y end).
Defined.

Definition inl {Γ} (A B : Typ Γ) (t : Trm Γ A) : Trm Γ (Sum A B).
Proof.
unshelve econstructor.
+ refine (fun γ => inl (t.(trm_fwd) γ)).
+ refine (fun γ π => t.(trm_bwd) γ π).
Defined.

Definition inr {Γ} (A B : Typ Γ) (t : Trm Γ B) : Trm Γ (Sum A B).
Proof.
unshelve econstructor.
+ refine (fun γ => inr (t.(trm_fwd) γ)).
+ refine (fun γ π => t.(trm_bwd) γ π).
Defined.

Definition elim_Sum {Γ} {A B : Typ Γ} (P : Typ (ext Γ (Sum A B)))
  (pl : Trm (ext Γ A) (typ_sub P (cns (A := Sum _ _)
    (wkn A (idn Γ)) (inl (typ_sub A (wkn A (idn Γ))) (typ_sub B (wkn A (idn Γ))) rel0))))
  (pr : Trm (ext Γ B) (typ_sub P (cns (A := Sum _ _)
    (wkn B (idn Γ)) (inr (typ_sub A (wkn B (idn Γ))) (typ_sub B (wkn B (idn Γ))) rel0))))
  (s : Trm Γ (Sum A B))
  :
    Trm Γ (typ_sub P (cns (A := Sum _ _) (idn _) s)).
Proof.
unshelve econstructor.
+ cbn.
  refine (fun γ =>
    match s.(trm_fwd) γ as s₀ return typ_wit P (pair γ s₀) with
    | Datatypes.inl x => pl.(trm_fwd) (pair γ x)
    | Datatypes.inr y => pr.(trm_fwd) (pair γ y)
    end).
+ cbn.
  refine (fun γ =>
    match s.(trm_fwd) γ as s₀ return

    forall (sb : typ_ctr (Sum A B) γ s₀ -> ctx_ctr Γ γ),

    typ_ctr P (pair γ s₀)
      match s₀ return typ_wit P (pair γ s₀) with
      | Datatypes.inl x => trm_fwd pl {| fst := γ; snd := x |}
      | Datatypes.inr y => trm_fwd pr {| fst := γ; snd := y |}
      end -> ctx_ctr Γ γ

  with

  | Datatypes.inl x => fun sb πl =>
    fst (pl.(trm_bwd) (pair γ x) πl) ⊕
    (Mlet (pl.(trm_bwd) (pair γ x) πl).(snd) sb)
  | Datatypes.inr y => fun sb πr =>
    fst (pr.(trm_bwd) (pair γ y) πr) ⊕
    (Mlet (pr.(trm_bwd) (pair γ y) πr).(snd) sb)
  end (s.(trm_bwd) γ)

  ).

Defined.

Lemma Sum_sub : forall Γ Δ (A B : Typ Γ) (σ : Sub Δ Γ), typ_sub (Sum A B) σ = Sum (typ_sub A σ) (typ_sub B σ).
Proof.
reflexivity.
Qed.

Lemma inl_sub : forall Γ Δ (A B : Typ Γ) (t : Trm Γ A) (σ : Sub Δ Γ),
  trm_sub (inl A B t) σ = inl (typ_sub A σ) (typ_sub B σ) (trm_sub t σ).
Proof.
reflexivity.
Qed.

Lemma inr_sub : forall Γ Δ (A B : Typ Γ) (t : Trm Γ B) (σ : Sub Δ Γ),
  trm_sub (inr A B t) σ = inr (typ_sub A σ) (typ_sub B σ) (trm_sub t σ).
Proof.
reflexivity.
Qed.

Lemma elim_Sum_sub : forall Γ Δ A B P pl pr s (σ : Sub Δ Γ),
  trm_sub (@elim_Sum Γ A B P pl pr s) σ =
  @elim_Sum Δ (typ_sub A σ) (typ_sub B σ) (typ_sub P (lft _ σ)) (trm_sub pl (lft _ σ)) (trm_sub pr (lft _ σ)) (trm_sub s σ).
Proof.
intros; unshelve eapply trm_eq_intro.
+ reflexivity.
+ cbn; intros γ.
  destruct s as [sf sb]; cbn.
  set (sb₀ := sb (sub_fwd σ γ)).
  set (sf₀ := sf (sub_fwd σ γ)) in sb₀ |- *.
  clearbody sb₀; clear sb.
  clearbody sf₀.
  destruct sf₀ as [x|y]; cbn.
  - cbn; intros.
    rewrite Sub_add; f_equal.
    unfold Mlet; now rewrite Sub_alg, map_map.
  - cbn; intros.
    rewrite Sub_add; f_equal.
    unfold Mlet; now rewrite Sub_alg, map_map.
Qed.

Lemma elim_Sum_inl : forall Γ A B P pl pr t,
  @elim_Sum Γ A B P pl pr (inl A B t) = trm_sub pl (cns (idn _) t).
Proof.
reflexivity.
Qed.

Lemma elim_Sum_inr : forall Γ A B P pl pr t,
  @elim_Sum Γ A B P pl pr (inr A B t) = trm_sub pr (cns (idn _) t).
Proof.
reflexivity.
Qed.

(** Universe.

  We simply store the W and C components of the type to code as a
  dependent pair, i.e.

  W(Type) := { W_A : Type; C_A : W_A → Type }.

  By contrast, we hardwire that codes do not use their arguments
  computationally by setting

  C(Type)[(W_A, C_A)] := False.

  As a result the backward component of a code is always trivial,
  at least extensionally so.

 *)

Definition Unv {Γ : Ctx} : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ => sig Type (fun A => A -> Type)).
+ refine (fun γ π => False).
Defined.

Definition Elt {Γ} (A : Trm Γ Unv) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ => (A.(trm_fwd) γ).(fst)).
+ refine (fun γ => (A.(trm_fwd) γ).(snd)).
Defined.

Definition Rpr {Γ} (A : Typ Γ) : Trm Γ Unv.
Proof.
unshelve econstructor.
+ refine (fun γ => pair (A.(typ_wit) γ) (A.(typ_ctr) γ)).
+ intros _ [].
Defined.

(** This is a Coquand universe, i.e. the above functions form
    an isomorphism. One side is even definitional. *)

Lemma Elt_Rpr_eqn : forall Γ (A : Typ Γ), Elt (Rpr A) = A.
Proof.
reflexivity.
Qed.

Lemma Rpr_Elt_eqn : forall Γ (A : Trm Γ Unv), Rpr (Elt A) = A.
Proof.
intros; unshelve eapply trm_eq_intro.
+ reflexivity.
+ cbn; intros γ [].
Qed.

(** Effects *)

(** The type Pack is basically a unary sum type. It embodies the
    implicit ambient CBPV comonad. *)

Definition Pack {Γ : Ctx} (A : Typ Γ) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ => A.(typ_wit) γ).
+ refine (fun γ π => M (A.(typ_ctr) γ π)).
Defined.

Definition pack {Γ : Ctx} {A : Typ Γ} (t : Trm Γ A) : Trm Γ (Pack A).
Proof.
unshelve econstructor.
+ refine (fun γ => t.(trm_fwd) γ).
+ refine (fun γ π => Mlet π (t.(trm_bwd) γ)).
Defined.

Definition elim_Pack {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ (Pack A))}
  (t : Trm Γ (Pack A))
  (u : Trm (ext Γ A) (typ_sub B (cns (A := Pack _) (wkn _ (idn _)) (pack rel0))))
  : Trm Γ (typ_sub B (cns (A := Pack A) (idn Γ) t)).
Proof.
unshelve econstructor.
+ refine (fun γ => u.(trm_fwd) (pair γ (t.(trm_fwd) γ))).
+ cbn. refine (fun γ π => _ ⊕ _).
  - refine (fst (u.(trm_bwd) (pair γ _) π)).
  - refine (t.(trm_bwd) γ _).
    refine (snd (u.(trm_bwd) (pair γ _) π)).
Defined.

Definition unpack {Γ : Ctx} {A B : Typ Γ}
  (t : Trm Γ (Pack A)) (u : Trm (ext Γ A) (typ_sub B (wkn _ (idn _)))) : Trm Γ B :=
  @elim_Pack Γ A (typ_sub B (wkn _ (idn _))) t u.

Lemma elim_Pack_pack : forall Γ A B t u,
  (@elim_Pack Γ A B (pack t) u) = trm_sub u (cns (idn _) t).
Proof.
reflexivity.
Qed.

(** A term x : A ⊢ t : B is linear in x whenever

    x₀ : Pack A ⊢ (let x := (let pack x := x₀ in x) in t) = (let pack x := x₀ in t)

    Surprisingly not all terms are linear in general, despite the fact
    that Pack has an induction principle stating that internally all
    terms of type Pack are introduced by a pack constructor.

*)

Definition linear {Γ : Ctx} {A B : Typ Γ} (t : Trm (ext Γ A) (typ_sub B (wkn _ (idn _)))) : Prop.
Proof.
refine (
  @trm_sub (ext Γ A) (ext Γ (Pack A)) _ t (cns (wkn _ (idn _))
    (@unpack (ext Γ (Pack A)) (typ_sub A _) _ rel0 rel0)) =
  @unpack (ext Γ (Pack A)) (typ_sub A _) _ rel0 _
).
refine (trm_sub t (lft _ (wkn _ (idn _)))).
Defined.

Lemma linear_intro : forall {Γ : Ctx} {A B : Typ Γ} (t : Trm (ext Γ A) (typ_sub B _)),
  (forall γ x π,
    map ret (snd (trm_bwd t (pair γ x) π)) = ret (snd (trm_bwd t (pair γ x) π))) ->
  linear t.
Proof.
intros * H; unshelve eapply trm_eq_intro.
+ reflexivity.
+ intros [γ x] π; cbn in *.
  apply prod_eq_intro; cbn.
  - rewrite map_map; f_equal; cbn.
    rewrite Alg_id_l; apply Mlet_nul.
  - rewrite !add_id_l, map_map; cbn.
    unfold map; rewrite !bind_assoc.
    match goal with [ |- bind _ ?f = _ ] => assert (e : f = (fun π => ret (ret π))) end.
    { clear; apply funext; intros π.
      now rewrite bind_ret_l, add_id_l. }
    rewrite e; clear e.
    apply H.
Qed.
