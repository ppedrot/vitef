Require Import syntax.

Ltac funext := apply FunctionalExtensionality.functional_extensionality_dep.

Set Primitive Projections.

Record Theory := {
  thy_idx : Set;
  thy_axm : forall i : thy_idx, form 0;
}.

Inductive In {A} (x : A) : list A -> Type :=
| In_here : forall l, In x (cons x l) 
| In_next : forall y l, In x l -> In x (cons y l).

Delimit Scope subst_scope with subst.

Definition lift_form {Σ : nat} (A : form Σ) : form (S Σ) :=
  subst_form (fun n => @var_term (S _) (Some n)) A.

Inductive proof (T : Theory) (Σ : nat) (Γ : list (form Σ)) : form Σ -> Type :=
| prf_thy :
  forall (i : T.(thy_idx)),
  proof T Σ Γ (subst_form null (T.(thy_axm) i))
| prf_axm :
  forall A, In A Γ -> proof T Σ Γ A
| prf_arr_i :
  forall A B, proof T Σ (cons A Γ) B -> proof T Σ Γ (Arr A B)
| prf_arr_e :
  forall A B, proof T Σ Γ (Arr A B) -> proof T Σ Γ A -> proof T Σ Γ B
| prf_top_i : proof T Σ Γ Top
| prf_bot_e : forall A, proof T Σ Γ Bot -> proof T Σ Γ A
| prf_cnj_i : forall A B,
  proof T Σ Γ A -> proof T Σ Γ B -> proof T Σ Γ (Cnj A B)
| prf_cnj_e₁ : forall A B,
  proof T Σ Γ (Cnj A B) -> proof T Σ Γ A
| prf_cnj_e₂ : forall A B,
  proof T Σ Γ (Cnj A B) -> proof T Σ Γ B
| prj_dsj_i₁ : forall A B,
  proof T Σ Γ A -> proof T Σ Γ (Dsj A B)
| prj_dsj_i₂ : forall A B,
  proof T Σ Γ B -> proof T Σ Γ (Dsj A B)
| prj_dsj_e : forall A B C,
  proof T Σ Γ (Dsj A B) -> proof T Σ (cons A Γ) C -> proof T Σ (cons B Γ) C -> proof T Σ Γ C
| prf_frl_i :
  forall (A : form (S Σ)), proof T (S Σ) (List.map lift_form Γ) A -> proof T Σ Γ (All A) 
| prf_frl_e :
  forall (A : form (S Σ)) (t : term Σ), proof T Σ Γ (All A) ->
  proof T Σ Γ (subst_form (t .: var_term) A)
| prf_exs_i :
  forall (A : form (S Σ)) (t : term Σ),
  proof T Σ Γ (subst_form (t .: var_term) A) -> proof T Σ Γ (Exs A)
| prf_exs_e :
  forall (A : form (S Σ)) (B : form Σ),
  proof T Σ Γ (Exs A) ->
  proof T (S Σ) (List.map lift_form Γ) (lift_form B) ->
  proof T Σ Γ B
.

Module Std.

Definition env (Σ : nat) := fin Σ -> term 0.

Section Std.

Variable ATOM : forall α : atom, (fin (atom_arity α) -> term 0) -> Prop.

Fixpoint interp {Σ : nat} (ρ : env Σ) (A : form Σ) : Prop :=
match A with
| Atm α args => ATOM α (fun n => subst_term ρ (args n))
| Arr A B => interp ρ A -> interp ρ B
| Top => True
| Bot => False
| Cnj A B => interp ρ A /\ interp ρ B
| Dsj A B => interp ρ A \/ interp ρ B
| All A => forall (t : term 0), interp (t .: ρ) A
| Exs A => exists (t : term 0), interp (t .: ρ) A
end.

Lemma interp_subst : forall Σ Σ' (ρ : env Σ) σ (A : form Σ'),
  interp ρ (subst_form σ A) <-> interp (σ >> subst_term ρ) A.
Proof.
intros Σ Σ' ρ σ A.
revert Σ ρ σ.
induction A; cbn in *; intros Σ ρ σ.
+ match goal with [ |- ATOM _ ?f <-> ATOM _ ?g ] => replace f with g; [tauto|] end.
  funext; intros n; unfold funcomp.
  unfold cod_map.
  symmetry; apply compSubstSubst_term; intros t.
  reflexivity.
+ rewrite IHA1, IHA2; reflexivity.
+ reflexivity.
+ reflexivity.
+ rewrite IHA1, IHA2; reflexivity.
+ rewrite IHA1, IHA2; reflexivity.
+ split; intros H t;
  specialize (IHA _ (t .: ρ) (up_term_term σ)).
  - destruct IHA as [IHA _].
    specialize (IHA (H _)).
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    clear.
    funext; intros n; unfold funcomp.
    destruct n as [n|]; cbn; [|reflexivity].
    fsimpl; f_equal.
    funext; intros m; unfold funcomp.
    rewrite compComp_term; cbn; reflexivity.
  - apply <- IHA.
    specialize (H t).
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    clear.
    funext; intros n; unfold funcomp.
    destruct n as [n|]; cbn; [|reflexivity].
    fsimpl; f_equal.
    funext; intros m; unfold funcomp.
    rewrite compComp_term; cbn; reflexivity.
+ split; intros [t Ht]; exists t.
  - apply IHA in Ht.
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    funext; intros [m|]; cbn; try reflexivity.
    unfold funcomp; rewrite compComp_term; cbn; reflexivity.
  - apply IHA.
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    funext; intros [m|]; cbn; try reflexivity.
    unfold funcomp; rewrite compComp_term; cbn; reflexivity.
Qed.

Variable T : Theory.

Variable T_sound : forall (i : T.(thy_idx)), interp null (T.(thy_axm) i).

Lemma interp_sound : forall Σ (ρ : env Σ) Γ (A : form Σ) (π : proof T Σ Γ A),
  List.Forall (fun A => interp ρ A) Γ -> interp ρ A.
Proof.
induction 1; intros γ; cbn.
+ apply interp_subst.
  replace (null >> subst_term ρ) with (@null (term 0)).
  - apply T_sound.
  - funext; intros [].
+ clear - i γ; induction i.
  - inversion γ; assumption.
  - inversion γ; subst; apply IHi; assumption.
+ intros x; apply IHπ; constructor; assumption.
+ cbn in IHπ1; apply IHπ1; [|apply IHπ2]; assumption.
+ constructor.
+ destruct (IHπ ρ); assumption.
+ split; intuition.
+ apply IHπ; assumption.
+ apply IHπ; assumption.
+ left; apply IHπ; assumption.
+ right; apply IHπ; assumption.
+ destruct (IHπ1 ρ γ); now intuition.
+ intros t; apply IHπ.
  clear - γ.
  induction γ; cbn; constructor; try assumption.
  clear - H.
  apply <- interp_subst.
  match goal with [ |- interp ?s _ ] => replace s with ρ; [assumption|] end.
  reflexivity.
+ cbn in IHπ.
  apply interp_subst; cbn.
  specialize (IHπ ρ γ (subst_term ρ t)).
  match goal with [ |- interp ?s _ ] => replace s with (subst_term ρ t .: ρ); [assumption|] end.
  cbn.
  funext; intros [m|]; reflexivity.
+ exists (subst_term ρ t).
  specialize (IHπ ρ γ).
  apply interp_subst in IHπ.
  match goal with [ |- interp ?s _ ] => replace s with ((t .: var_term) >> subst_term ρ); [assumption|] end.
  funext; intros [m|]; reflexivity.
+ specialize (IHπ1 ρ γ); destruct IHπ1 as [t Ht].
  specialize (IHπ2 (t .: ρ)).
  match type of IHπ2 with ?T -> _ => assert T end.
  { clear - γ; induction γ; cbn in *; constructor.
    - unfold lift_form.
      apply interp_subst; cbn.
      apply H.
    - intuition.
  }
  specialize (IHπ2 H).
  unfold lift_form in IHπ2; apply interp_subst in IHπ2.
  apply IHπ2.
Qed.

Lemma proof_consistent : proof T 0 nil Bot -> False.
Proof.
intros π.
refine (interp_sound _ null _ _ π _).
constructor.
Qed.

End Std.

Module Dynamic.

Definition atomic Σ := { a : atom & fin (atom_arity a) -> term Σ }.

Definition subst_atomic {Σ Σ' : nat} (σ : fin Σ -> term Σ') (a : atomic Σ) : atomic Σ' :=
match a with
| existT _ α args => existT _ α (fun n => subst_term σ (args n))
end.

Definition nlift_atomic {Σ} Σ' (a : atomic Σ) : atomic (Σ' + Σ) :=
  subst_atomic (shift_p Σ' >> var_term) a.

Definition mAtm {Σ} (a : atomic Σ) : form Σ :=
match a with existT _ α args => Atm α args end.

Fixpoint nAll (Σ : nat) (A : form Σ) : form 0 :=
match Σ return form Σ -> form 0 with
| 0 => fun A => A
| S Σ => fun A => nAll Σ (All A)
end A.

Fixpoint nCnj {Σ : nat} (Φ : list (atomic Σ)) : form Σ := match Φ with
| nil => Top
| cons A Φ => Cnj (mAtm A) (nCnj Φ)
end.

Fixpoint nExs {Σ Σ' : nat} (A : form (Σ' + Σ)) : form Σ :=
match Σ' return form (Σ' + Σ) -> form Σ with
| 0 => fun A => A
| S Σ' => fun A => nExs (Exs A)
end A.

Fixpoint nSplit {Σ : nat} (Ψ : list {Σ' : nat & list (atomic (Σ' + Σ))}) : form Σ := match Ψ with
| nil => Bot
| cons (existT _ Σ' Φ) Ψ => Dsj (nExs (nCnj Φ)) (nSplit Ψ)
end.

Record geometric := {
  geom_ctx : nat;
  geom_hyp : list (atomic geom_ctx);
  geom_ccl : list {Σ : nat & list (atomic (Σ + geom_ctx))};
}.

Definition of_geometric (G : geometric) : form 0 :=
  nAll G.(geom_ctx) (Arr (nCnj G.(geom_hyp)) (nSplit G.(geom_ccl))).

Record GTheory := {
  gthy_idx : Set;
  gthy_axm : forall (i : gthy_idx), geometric;
}.

Definition of_gtheory (T : GTheory) : Theory := {|
  thy_idx := T.(gthy_idx);
  thy_axm := fun i => of_geometric (T.(gthy_axm) i);
|}.

Record ℙ := mkℙ {
  idxℙ : nat;
  ctxℙ : list (atomic idxℙ);
}.

Inductive extends (p : ℙ) : ℙ -> Type :=
| Extends : forall (Σ : nat) (Ω : list (atomic (Σ + p.(idxℙ)))),
  extends p (mkℙ (Σ + p.(idxℙ)) (app Ω (List.map (nlift_atomic _) p.(ctxℙ)))).

Definition extends_one : forall Ω, extends Ω Ω.
Proof.
intros Ω.
set (Ω₀ := Ω) at 1.
destruct Ω as [Σ Ω].
replace Ω with (List.map (nlift_atomic 0) Ω).  
+ refine (Extends _ 0 nil).
+ clear; induction Ω.
  - reflexivity.
  - cbn; f_equal; try assumption.
    destruct a as [a args].
    unfold nlift_atomic; cbn; f_equal.
    funext; intros n; cbn.
    apply idSubst_term; reflexivity.
Qed.

Definition extends_cmp : forall Ω Ω' Ω'', extends Ω Ω' -> extends Ω' Ω'' -> extends Ω Ω''.
Proof.
intros Ω Ω' Ω'' α β.
destruct α as [Σ Θ]; destruct β as [Σ' Θ']; cbn in *.
rewrite map_app, app_assoc.
rewrite map_map.
set (Ξ := list_map (nlift_atomic Σ') Θ); clearbody Ξ; clear Θ; rename Ξ into Θ.
revert Θ Θ'.
Admitted.

Definition le (p q : ℙ) := forall (r : ℙ), extends p r -> extends q r.

Notation "p ≤ q" := (le p q) (at level 70).

Definition le_one {p} : le p p := fun r k => k.
Definition le_cmp {p q r} (β : le r q) (α : le q p) : le r p := fun r k => α _ (β _ k).

Notation "!" := le_one.
Notation "α ∘ β" := (le_cmp α β) (at level 35).
Notation "α · t" := (fun r β => t r (β ∘ α)) (at level 35).

Definition le_of {Ω Ω'} (α : extends Ω Ω') : le Ω' Ω :=
  fun r β => extends_cmp _ _ _ α β.

Definition le_to {Ω Ω'} (α : le Ω' Ω) : extends Ω Ω' := α _ (extends_one _).

Definition isMon₀ {Ω} (A : forall Ω', Ω' ≤ Ω -> Type) :=
  forall Ω' Ω'' (α : Ω' ≤ Ω) (β : Ω'' ≤ Ω'), A Ω' α -> A Ω'' (β ∘ α).

Definition isMon {Ω} (A : forall Ω', Ω' ≤ Ω -> Type) :=
  forall Ω' Ω'' (α : Ω' ≤ Ω) (β : Ω'' ≤ Ω'), A Ω' α -> A Ω'' (β ∘ α).

Section Interp.

Variable T : GTheory.

Inductive Forall {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_nil : Forall P nil
| Forall_cons : forall (x : A) (l : list A),
  P x -> Forall P l -> Forall P (x :: l).

Lemma Forall_map {A} {P Q : A -> Type} (f : forall x, P x -> Q x)
  (l : list A) (p : Forall P l) : Forall Q l.
Proof.
induction p; constructor.
+ apply f; assumption.
+ assumption.
Qed.

Lemma Forall_map_nat {A B} {P : B -> Type} (f : A -> B)
  (l : list A) (p : Forall (fun x => P (f x)) l) : Forall P (List.map f l).
Proof.
induction p.
+ constructor.
+ cbn; constructor; assumption.
Qed.

Fixpoint nth {A} (l : list A) (i : fin (length l)) : A :=
match l return fin (length l) -> A with
| nil => fun (i : False) => match i with end
| cons x l =>
  fun i => match i with
  | None => x
  | Some i => nth l i
  end
end i.

Definition enrich {Σ} (Ω : ℙ) (ρ : fin Σ -> term Ω.(idxℙ))
  (ψ : {Σ' : nat & list (atomic (Σ' + Σ))}) : ℙ.
Proof.
destruct Ω as [Θ Ω].
unshelve refine (mkℙ (projT1 ψ + Θ) (app (List.map (subst_atomic (upList_term_term _ ρ)) (projT2 ψ)) (List.map (nlift_atomic _) Ω))).
Defined.

Definition enrich_extends {Σ} Ω ρ ψ : extends Ω (@enrich Σ Ω ρ ψ).
Proof.
constructor.
Defined.

Definition enrich_le {Σ} Ω ρ ψ := le_of (@enrich_extends Σ Ω ρ ψ).

Definition lift_le {Σ Ω Ω'} (ρ : fin Σ -> term Ω.(idxℙ)) (α : Ω' ≤ Ω) : fin Σ -> term Ω'.(idxℙ).
Proof.
refine (ρ >> subst_term _).
clear - α.
intros n.
refine (
  match le_to α in extends _ Ω' return term Ω'.(idxℙ) with
  | Extends _ Σ Θ => _
  end
).
cbn.
refine ((shift_p Σ >> var_term) n).
Defined.

Lemma lift_le_unique : forall Σ Ω Ω' (ρ : fin Σ -> term Ω.(idxℙ)) (α α' : Ω' ≤ Ω),
  lift_le ρ α = lift_le ρ α'.
Proof.
intros Σ Ω Ω' ρ α α'.
funext; intros n; unfold lift_le, funcomp; cbn.
f_equal; clear; funext; intros n.
destruct (le_to α).
Admitted.

Lemma lift_le_cmp : forall {Σ Ω Ω' Ω''} (ρ : fin Σ -> term Ω.(idxℙ)) (α : Ω' ≤ Ω) (β : Ω'' ≤ Ω'),
  lift_le ρ (β ∘ α) = lift_le (lift_le ρ α) β.
Proof.
intros; funext; intros n.
assert (δ := β ∘ α).
rewrite (lift_le_unique _ _ _ _ (β ∘ α) δ).
unfold lift_le; cbn.
unfold le_to, le_cmp.
destruct (β Ω'' (extends_one _)); cbn.
Admitted.

Lemma lift_le_id : forall {Σ Ω} (ρ : fin Σ -> term Ω.(idxℙ)),
  lift_le ρ ! = ρ.
Proof.
intros; funext; intros n.
unfold lift_le; cbn.
unfold le_to, funcomp; unfold le_one at 1; cbn.
apply idSubst_term; clear; intros n.
pose (e := Extends Ω 0 nil).
Admitted.

Lemma lift_le_nat : forall Σ Σ' Ω Ω' (α : Ω' ≤ Ω)
  (ρ : fin Σ -> term (idxℙ Ω))
  (σ : fin Σ' -> term Σ),
  (σ >> subst_term (lift_le ρ α)) = (lift_le (σ >> (subst_term ρ)) α).
Proof.
intros Σ Σ' Ω Ω' α ρ σ.
funext; intros n.
unfold funcomp, lift_le; cbn.
destruct (le_to α).
rewrite compComp_term; reflexivity.
Qed.

Definition InΩ {Σ} Ω (ρ : fin Σ -> term Ω.(idxℙ)) (a : atomic Σ) Ω' (α : Ω' ≤ Ω) :=
 In (subst_atomic (lift_le ρ α) a) Ω'.(ctxℙ).

Lemma In_app_r : forall (A : Type) (l1 l2 : list A) (x : A),
  In x l2 -> In x (app l1 l2).
Proof.
induction l1; intros l2 x H; cbn in *; [assumption|].
constructor; apply IHl1, H.
Qed.

Lemma In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (List.map f l).
Proof.
induction 1; constructor; assumption.
Qed.

Lemma InΩ_isMon : forall Σ Ω ρ (a : atomic Σ),
  isMon (fun (Ω' : ℙ) (α : Ω' ≤ Ω) => InΩ Ω ρ a Ω' α).
Proof.
intros Σ Ω ρ a Ω' Ω'' α β i.
unfold InΩ in *.
assert (β₀ := le_to β); destruct β₀ as [Σ' Θ]; cbn in *.
apply In_app_r.
match goal with [ |- In ?x _ ] =>
  replace x with (nlift_atomic Σ' (subst_atomic (lift_le ρ α) a))
end.
{ apply In_map, i. }
clear i. destruct a as [a args]; cbn in *.
f_equal; funext; intros n.
rewrite compComp_term; f_equal.
rewrite lift_le_cmp.
clear n; funext; intros n.
Admitted.

Inductive Dyn (Ω : ℙ) (A : forall Ω', Ω' ≤ Ω -> Type) :=
| ret : A Ω ! -> Dyn Ω A
| ask : forall
  (i : T.(gthy_idx))
  (G := T.(gthy_axm) i)
  (ρ : fin G.(geom_ctx) -> term Ω.(idxℙ)),
  Forall (fun a => forall Ω' α, InΩ Ω ρ a Ω' α) G.(geom_hyp) ->
  forall (k : forall i : fin (length (G.(geom_ccl))),
    let ψ := nth G.(geom_ccl) i in
    forall Ω' (α : Ω' ≤ Ω),
    Dyn (enrich Ω' (lift_le ρ α) ψ) (enrich_le Ω' (lift_le ρ α) ψ ∘ α · A)),
  Dyn Ω A
.

Definition Dyn_bind {Ω}
  {A B : forall Ω', Ω' ≤ Ω -> Type}
  (m : Dyn Ω A)
  (f : forall Ω' (α : Ω' ≤ Ω), A Ω' α -> Dyn Ω' (α · B)) :
  Dyn Ω B.
Proof.
revert B f.
induction m as [Ω A x|Ω A i G ρ H k bind]; intros B F.
+ refine (F Ω ! x).
+ unshelve refine (ask _ _ i ρ H _).
  intros o ψ Ω' α.
  refine (bind _ _ _ _ _).
  intros Ω'' β x.
  refine (F _ _ x).
Defined.

Lemma isMon_cmp : forall Ω Ω' A α, @isMon Ω A -> @isMon Ω' (α · A).
Proof.
intros.
intros Ω'' Ω''' β γ x.
unfold isMon in X.
refine (X _ _ _ _ x).
Defined.

Definition Dyn_map {Ω A B} (f : forall Ω' (α : Ω' ≤ Ω), A Ω' α -> B Ω' α) (x : Dyn Ω A) : Dyn Ω B :=
  @Dyn_bind Ω A B x (fun Ω' α x => ret _ _ (f _ _ x)).

Lemma Dyn_isMon : forall Ω A, @isMon Ω A -> isMon (fun Ω' α => Dyn Ω' (α · A)).
Proof.
intros Ω A θA.
intros Ω' Ω'' α β x.
revert β.
apply (isMon_cmp _ _ _ α) in θA.
change (forall β, Dyn Ω'' (β · (α · A))).
set (A₀ := α · A) in *; clearbody A₀; clear Ω α A; rename A₀ into A.
revert Ω''.
induction x as [Ω A a|Ω A i G ρ H k θDyn].
+ intros Ω' α.
  refine (ret _ _ (θA _ _ _ _ a)).
+ intros Ω' α.
  unshelve refine (ask _ _ i _ _ _).
  - refine (lift_le ρ α).
  - clear - H.
    refine (Forall_map _ _ H); clear; intros [a args] H; cbn in *.
    intros Ω'' β.
    unfold InΩ in H |- *.
    rewrite <- lift_le_cmp.
    refine (H Ω'' (β ∘ α)).
  - intros o ψ Ω'' β; cbn.
    specialize (θDyn o Ω'' (β ∘ α) (isMon_cmp _ _ _ _ θA)).
    set (σ := (lift_le (lift_le ρ α) β)).
    change (Dyn (enrich Ω'' σ ψ) (((enrich_le Ω'' σ ψ ∘ β)) ∘ α · A)).
    replace σ with (lift_le ρ (β ∘ α)) by apply lift_le_cmp.
    refine (θDyn _ !).
Qed.

Fixpoint interp {Σ} (A : form Σ) {Ω : ℙ} (ρ : fin Σ -> term Ω.(idxℙ)) {struct A} : Type := 
match A with
| Atm a args => Dyn Ω (fun Ω' α => InΩ Ω ρ (existT _ a args) Ω' α)
| Arr A B =>
  forall Ω' (α : Ω' ≤ Ω), interp A (lift_le ρ α) -> interp B (lift_le ρ α)
| Top => True
| Bot => Dyn Ω (fun Ω' α => False)
| Cnj A B => prod (interp A ρ) (interp B ρ)
| Dsj A B => Dyn Ω (fun Ω' α => interp A (lift_le ρ α) + interp B (lift_le ρ α))%type
| All A =>
  forall Ω' (α : Ω' ≤ Ω) (t : term Ω'.(idxℙ)), interp A (t .: lift_le ρ α)
| Exs A =>
  Dyn Ω (fun Ω' α => { t : term Ω'.(idxℙ) & interp A (t .: lift_le ρ α) })
end.

Definition iffT (A B : Type) := prod (A -> B) (B -> A).

Lemma interp_subst : forall Σ Σ' (A : form Σ') Ω (ρ : fin Σ -> term Ω.(idxℙ)) σ,
  iffT (interp (subst_form σ A) ρ) (interp A (σ >> subst_term ρ)).
Proof.
intros Σ Σ' A; revert Σ; induction A; intros Σ Ω ρ σ; split; cbn in *.
+ refine (Dyn_map _).
  unfold InΩ; intros Ω' α i; cbn in *.
  match goal with [ H : In (existT _ a ?p) _ |- In (existT _ a ?q) _ ] => replace q with p; [assumption|] end.
  funext; intros n; cbn; unfold cod_map.
  rewrite <- lift_le_nat, compComp_term; reflexivity.
+ refine (Dyn_map _).
  unfold InΩ; intros Ω' α i; cbn in *.
  match goal with [ H : In (existT _ a ?p) _ |- In (existT _ a ?q) _ ] => replace q with p; [assumption|] end.
  funext; intros n; cbn; unfold cod_map.
  rewrite <- lift_le_nat, compComp_term; reflexivity.
+ intros f Ω' α x; cbn in *.
  rewrite <- lift_le_nat.
  apply IHA2, f.
  rewrite <- lift_le_nat in x.
  apply IHA1, x.
+ intros f Ω' α x; cbn in *.
  apply IHA2.
  rewrite lift_le_nat.
  apply f; rewrite <- lift_le_nat; apply IHA1, x.
+ intros; constructor.
+ intros; constructor.
+ refine (Dyn_map _); intros _ _ [].
+ refine (Dyn_map _); intros _ _ [].
+ intros [x y]; split; first [apply IHA1|apply IHA2]; assumption.
+ intros [x y]; split; first [apply IHA1|apply IHA2]; assumption.
+ refine (Dyn_map _); intros Ω' α [x|y];
  rewrite <- lift_le_nat;
  [left; apply IHA1|right; apply IHA2]; assumption.
+ refine (Dyn_map _); intros Ω' α [x|x];
  rewrite <- lift_le_nat in x;
  [left; apply IHA1|right; apply IHA2]; assumption.
+ intros f Ω' α t.
  specialize (f Ω' α t).
  apply IHA in f.
  rewrite <- lift_le_nat.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  funext; intros [n|]; cbn in *; [|reflexivity].
  unshelve apply compComp_term.
+ intros f Ω' α t.
  specialize (f Ω' α t).
  apply IHA.
  rewrite <- lift_le_nat in f.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  funext; intros [n|]; cbn in *; [|reflexivity].
  symmetry; unshelve apply compComp_term.
+ refine (Dyn_map _); intros Ω' α [t p]; exists t.
  apply IHA in p.
  rewrite <- lift_le_nat.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  funext; intros [n|]; cbn in *; [|reflexivity].
  unshelve apply compComp_term.
+ refine (Dyn_map _); intros Ω' α [t p]; exists t.
  apply IHA.
  rewrite <- lift_le_nat in p.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  funext; intros [n|]; cbn in *; [|reflexivity].
  symmetry; unshelve apply compComp_term.
Qed.

Lemma interp_isMon : forall Σ A Ω ρ, isMon (fun Ω' (α : Ω' ≤ Ω) => @interp Σ A Ω' (lift_le ρ α)).
Proof.
intros Σ A Ω ρ Ω' Ω'' α β x.
rewrite lift_le_cmp.
set (ρ₀ := lift_le ρ α) in *; clearbody ρ₀; clear - x.
rename Ω' into Ω, Ω'' into Ω', ρ₀ into ρ, β into α.
revert Ω Ω' α ρ x; induction A; intros Ω Ω' α ρ x; cbn in *.
+ match type of x with Dyn _ ?A =>
  unshelve refine (let x := Dyn_isMon _ A _ _ _ ! α x in _); [|clearbody x; cbn in x]
  end.
  { apply InΩ_isMon. }
  refine (Dyn_map (fun Ω'' β  => _) x); unfold InΩ in *.
  rewrite <- lift_le_cmp; clear; intro x; exact x.
+ intros Ω'' β x₀.
  rewrite <- lift_le_cmp; apply x; rewrite lift_le_cmp; assumption.
+ constructor.
+ refine (Dyn_isMon _ (fun _ _ => False) _ _ _ ! α x).
  clear; intros Ω' Ω'' α β [].
+ split; [apply IHA1|apply IHA2]; apply x.
+ match type of x with Dyn _ ?A =>
  unshelve refine (let x := Dyn_isMon _ A _ _ _ ! α x in _); [|clearbody x; cbn in x]
  end.
  { clear - IHA1 IHA2.
    intros Ω' Ω'' α β [x|y]; rewrite lift_le_cmp.
    + left; apply IHA1, x.
    + right; apply IHA2, y. }
  refine (Dyn_map _ x); clear.
  intros Ω'' β; rewrite lift_le_cmp; intros [x|y]; constructor; assumption.
+ intros Ω'' β t.
  rewrite <- lift_le_cmp.
  apply x.
+ admit.
Admitted.

Lemma interp_alg {Σ} (A : form Σ) {Ω} ρ
  (x : Dyn Ω (fun Ω' α => interp A (lift_le ρ α))) : interp A ρ.
Proof.
revert Ω ρ x; induction A; intros Ω ρ p; cbn in *.
+ refine (Dyn_bind p (fun Ω' α x => _)).
  admit.
+ intros Ω' α x.
  apply IHA2.
  admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
Admitted.

Lemma interp_nAll : forall Σ (A : form Σ) Ω (ρ : fin 0 -> term Ω.(idxℙ)),
  (forall Ω' (α : Ω' ≤ Ω) σ, @interp Σ A Ω' σ) -> interp (nAll Σ A) ρ.
Proof.
induction Σ as [|Σ IHΣ]; intros A Ω ρ p; cbn.
+ specialize (p Ω !); apply p.
+ apply IHΣ; intros Ω' α σ; cbn; intros Ω'' β t.
  apply p, (β ∘ α).
Defined.

Lemma interp_nSplit : forall Σ Ψ Ω (ρ : fin Σ -> term Ω.(idxℙ)) (o : fin (length Ψ)),
  match nth Ψ o with existT _ Σ' Φ => { σ : _ & @interp _ (nCnj Φ) Ω (scons_p _ σ ρ) } end ->
  interp (@nSplit Σ Ψ) ρ.
Proof.
induction Ψ as [|[Σ' Φ] Ψ IHΨ]; intros Ω ρ o p; cbn in *.
+ destruct o.
+ destruct o as [o|].
  - apply ret; right; rewrite lift_le_id.
    apply (IHΨ _ _ o), p.
  - apply ret; left; rewrite lift_le_id.
    destruct p as [σ p].
    clear - σ p; set (Ψ := nCnj Φ) in *; clearbody Ψ; clear Φ; rename Ψ into Φ.
    { revert Σ Ω ρ Φ σ p; induction Σ' as [|Σ' IHΣ']; intros Σ Ω ρ Φ σ p; cbn in *.
      + assumption.
      + unshelve refine (IHΣ' _ _ _ _ (Some >> σ) _).
        cbn; apply ret; exists (σ None).
        rewrite lift_le_id; apply p.
    }
Defined.

Lemma interp_oracle : forall Σ (Ω : ℙ) ρ (a : atomic Σ),
  In (subst_atomic ρ a) Ω.(ctxℙ) -> @interp Σ (mAtm a) Ω ρ.
Proof.
intros Σ Ω ρ [a args] Ha; cbn in *.
apply ret; unfold InΩ.
rewrite lift_le_id; apply Ha.
Defined.

Lemma interp_nCnj_of : forall Σ (Φ : list (atomic Σ)) Ω (ρ : fin Σ -> term Ω.(idxℙ)),
  interp (nCnj Φ) ρ ->
  Dyn Ω (fun Ω' α => Forall (fun φ => In (subst_atomic (lift_le ρ α) φ) Ω'.(ctxℙ)) Φ).
Proof.
intros Σ Φ; induction Φ as [|[a args] Φ IHΦ]; intros Ω ρ p; cbn in *.
+ apply ret; constructor.
+ destruct p as [x p]; cbn in *.
  apply IHΦ in p.
  refine (Dyn_bind p _); clear p; intros Ω' α p.
  unshelve refine (Dyn_bind (Dyn_isMon _ _ _ _ _ ! α x) _); clear x.
Admitted.

Lemma interp_geometric_axiom :
  forall (i : gthy_idx T) (Ω : ℙ) (ρ : fin 0 -> term (idxℙ Ω)),
    interp (of_geometric (gthy_axm T i)) ρ.
Proof.
intros i Ω ρ.
set (φ := gthy_axm T i).
unfold of_geometric.
apply interp_nAll; intros Ω' α σ; cbn; intros Ω'' β H.
apply interp_alg.
(* apply interp_nCnj_of in H. *)
(* refine (Dyn_bind H _); clear H; intros Ω''' δ H. *)
unshelve refine (ask _ _ i (lift_le σ β) _ _); fold φ.
- revert H.
  set (Φ := geom_hyp φ); clearbody Φ;
  set (Σ' := geom_ctx φ) in *; clearbody Σ'; clear.
  { induction Φ as [|A Φ]; cbn; intro H; constructor.
    + intros Ω''' δ; unfold InΩ.
      rewrite <- lift_le_cmp.
      destruct H as [H _]; destruct A as [a args]; cbn in *.
      
      admit.
    + apply IHΦ, H.
  }
- intros o ψ Ω''' δ.
  apply ret; apply interp_nSplit with o.
  fold ψ; destruct ψ as [Σ' Φ]; cbn.
  exists (zero_p _ >> var_term).
  rewrite <- !lift_le_cmp.
  admit.
Admitted.

Lemma interp_sound : forall Σ Γ (A : form Σ) Ω (ρ : fin Σ -> term Ω.(idxℙ)),
  proof (of_gtheory T) Σ Γ A -> Forall (fun X => interp X ρ) Γ -> interp A ρ.
Proof.
intros Σ Γ A Ω ρ π; revert Ω ρ; induction π; intros Ω ρ γ; cbn in *.
+ apply interp_subst.
  apply interp_geometric_axiom.
+ induction i; cbn in *.
  - inversion γ; subst; assumption.
  - apply IHi; inversion γ; subst; assumption.
+ intros Ω' α x.
  apply IHπ; constructor.
  - assumption.
  - refine (Forall_map (fun A x => _) _ γ).
    cbn in x; replace ρ with (lift_le ρ !) in x by apply lift_le_id.
    refine (interp_isMon _ _ _ _ _ _ ! α x).
+ specialize (IHπ1 Ω ρ γ Ω !).
  rewrite lift_le_id in IHπ1.
  specialize (IHπ2 Ω ρ γ).
  apply IHπ1, IHπ2.
+ constructor.
+ apply interp_alg.
  refine (Dyn_map _ (IHπ _ ρ γ)).
  intros _ _ [].
+ split.
  - apply IHπ1, γ.
  - apply IHπ2, γ.
+ apply IHπ, γ.
+ apply IHπ, γ.
+ apply ret; left; rewrite lift_le_id.
  apply IHπ, γ.
+ apply ret; right; rewrite lift_le_id.
  apply IHπ, γ.
+ apply interp_alg.
  refine (Dyn_map _ (IHπ1 _ _ γ)).
  intros Ω' α [x|y].
  - apply IHπ2; constructor; [assumption|].
    refine (Forall_map (fun A x => _) _ γ).
    cbn in x; replace ρ with (lift_le ρ !) in x by apply lift_le_id.
    refine (interp_isMon _ _ _ _ _ _ ! α x).
  - apply IHπ3; constructor; [assumption|].
    refine (Forall_map (fun A x => _) _ γ).
    cbn in x; replace ρ with (lift_le ρ !) in x by apply lift_le_id.
    refine (interp_isMon _ _ _ _ _ _ ! α x).
+ intros Ω' α t.
  unshelve refine (IHπ _ _ _).
  refine (Forall_map_nat _ _ _).
  refine (Forall_map (fun A x => _) _ γ); cbn in x.
  apply interp_subst.
  unshelve refine (interp_isMon _ _ _ _ _ _ ! _ _).
  rewrite lift_le_id.
  assumption.
+ specialize (IHπ Ω ρ γ Ω ! (subst_term ρ t)).
  apply interp_subst.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.  
  rewrite lift_le_id.
  funext; intros [n|]; reflexivity.
+ apply ret.
  exists (subst_term ρ t).
  specialize (IHπ Ω ρ γ).
  apply interp_subst in IHπ.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.  
  rewrite lift_le_id.
  funext; intros [n|]; reflexivity.
+ specialize (IHπ1 _ _ γ).
  apply interp_alg.
  refine (Dyn_map _ IHπ1); intros Ω' α [t p].
  specialize (IHπ2 Ω' (t .: lift_le ρ α)).
  admit.
Admitted.

End Dynamic.
