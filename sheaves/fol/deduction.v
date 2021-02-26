Require List Eqdep_dec Lia.
Require Import seq syntax.

Lemma nat_uip : forall (m n : nat) (p q : m = n), p = q.
Proof.
intros; apply Eqdep_dec.UIP_dec.
decide equality.
Qed.

Set Primitive Projections.

Record Theory := {
  thy_idx : Set;
  thy_axm : forall i : thy_idx, form 0;
}.

Inductive In {A} (x : A) : list A -> Type :=
| In_here : forall l, In x (cons x l) 
| In_next : forall y l, In x l -> In x (cons y l).

Definition lift_form {Σ : nat} (A : form Σ) : form (S Σ) :=
  subst_form (seq_init (fun n => @var_term (S _) (Some n))) A.

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
  proof T Σ Γ (subst_form (scons t (seq_init var_term)) A)
| prf_exs_i :
  forall (A : form (S Σ)) (t : term Σ),
  proof T Σ Γ (subst_form (scons t (seq_init var_term)) A) -> proof T Σ Γ (Exs A)
| prf_exs_e :
  forall (A : form (S Σ)) (B : form Σ),
  proof T Σ Γ (Exs A) ->
  proof T (S Σ) (List.map lift_form Γ) (lift_form B) ->
  proof T Σ Γ B
.


Lemma map_init_eta : forall Σ Σ' t (ρ : seq (term Σ) Σ'),
  seq_init (funcomp var_term shift) >> scons t ρ = ρ.
Proof.
intros.
rewrite map_init; apply nth_ext; intros n.
rewrite nth_init; reflexivity.
Qed.

Lemma map_init_eta_p : forall Σ Σ'' Σ' σ (ρ : seq (term Σ) Σ'),
  seq_init (funcomp var_term (shift_p Σ'')) >> seq_app σ ρ = ρ.
Proof.
intros.
apply nth_ext; intros p; rewrite nth_map, nth_init.
unfold funcomp; cbn; rewrite nth_shift_p; reflexivity.
Qed.

Module Std.

Definition env (Σ : nat) := seq (term 0) Σ.

Section Std.

Variable ATOM : forall α : atom, (seq (term 0) (atom_arity α)) -> Prop.

Fixpoint interp {Σ : nat} (ρ : env Σ) (A : form Σ) : Prop :=
match A with
| Atm α args => ATOM α (args >> ρ)
| Arr A B => interp ρ A -> interp ρ B
| Top => True
| Bot => False
| Cnj A B => interp ρ A /\ interp ρ B
| Dsj A B => interp ρ A \/ interp ρ B
| All A => forall (t : term 0), interp (scons t ρ) A
| Exs A => exists (t : term 0), interp (scons t ρ) A
end.

Lemma interp_subst : forall Σ Σ' (ρ : env Σ) σ (A : form Σ'),
  interp ρ (subst_form σ A) <-> interp (σ >> ρ) A.
Proof.
intros Σ Σ' ρ σ A.
revert Σ ρ σ.
induction A; cbn in *; intros Σ ρ σ.
+ match goal with [ |- ATOM _ ?f <-> ATOM _ ?g ] => replace f with g; [tauto|] end.
  apply nth_ext; intros p.
  rewrite !nth_map, compComp_term; reflexivity.
+ rewrite IHA1, IHA2; reflexivity.
+ reflexivity.
+ reflexivity.
+ rewrite IHA1, IHA2; reflexivity.
+ rewrite IHA1, IHA2; reflexivity.
+ split; intros H t;
  specialize (IHA _ (scons t ρ) (up_term_term σ)).
  - destruct IHA as [IHA _].
    specialize (IHA (H _)).
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    clear.
    apply nth_ext; intros [n|]; simpl; [|reflexivity].
    rewrite !nth_map, compComp_term, map_init_eta; reflexivity.
  - apply <- IHA.
    specialize (H t).
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    clear.
    apply nth_ext; intros [n|]; simpl; [|reflexivity].
    rewrite seq_map_map, !nth_map, compComp_term, map_init_eta; reflexivity.
+ split; intros [t Ht]; exists t.
  - apply IHA in Ht.
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    apply nth_ext; intros [n|]; simpl; [|reflexivity].
    rewrite seq_map_map, !nth_map.
    rewrite compComp_term, map_init_eta; reflexivity.
  - apply IHA.
    match goal with [ H : interp ?s _ |- interp ?t _ ] => replace t with s; [assumption|] end.
    apply nth_ext; intros [n|]; simpl; [|reflexivity].
    rewrite seq_map_map, !nth_map, compComp_term, map_init_eta; reflexivity.
Qed.

Variable T : Theory.

Variable T_sound : forall (i : T.(thy_idx)), interp null (T.(thy_axm) i).

Lemma interp_sound : forall Σ (ρ : env Σ) Γ (A : form Σ) (π : proof T Σ Γ A),
  List.Forall (fun A => interp ρ A) Γ -> interp ρ A.
Proof.
induction 1; intros γ; cbn.
+ apply interp_subst.
  simpl; apply T_sound.
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
  rewrite map_init_eta; reflexivity.
+ cbn in IHπ.
  apply interp_subst; simpl.
  specialize (IHπ ρ γ (subst_term ρ t)).
  match goal with [ |- interp ?s _ ] => replace s with (scons (subst_term ρ t) ρ); [assumption|] end.
  apply nth_ext; intros [m|]; simpl; [|reflexivity].
  rewrite varL_term; reflexivity.
+ exists (subst_term ρ t).
  specialize (IHπ ρ γ).
  apply interp_subst in IHπ.
  match goal with [ |- interp ?s _ ] => replace s with ((scons t (seq_init var_term)) >> ρ); [assumption|] end.
  apply nth_ext; intros [m|]; simpl; [|reflexivity].
  rewrite varL_term; reflexivity.
+ specialize (IHπ1 ρ γ); destruct IHπ1 as [t Ht].
  specialize (IHπ2 (scons t ρ)).
  match type of IHπ2 with ?T -> _ => assert T end.
  { clear - γ; induction γ; cbn in *; constructor.
    - unfold lift_form.
      apply interp_subst; cbn.
      rewrite map_init_eta; apply H.
    - intuition.
  }
  specialize (IHπ2 H).
  unfold lift_form in IHπ2; apply interp_subst in IHπ2.
  rewrite map_init_eta in IHπ2; apply IHπ2.
Qed.

Lemma proof_consistent : proof T 0 nil Bot -> False.
Proof.
intros π.
refine (interp_sound _ null _ _ π _).
constructor.
Qed.

End Std.

End Std.


Module Dynamic.

Definition atomic Σ := { a : atom & seq (term Σ) (atom_arity a) }.

Definition subst_atomic {Σ Σ' : nat} (σ : seq (term Σ') Σ) (a : atomic Σ) : atomic Σ' :=
match a with
| existT _ α args => existT _ α (args >> σ)
end.

Definition nlift_atomic {Σ} Σ' (a : atomic Σ) : atomic (Σ' + Σ) :=
  subst_atomic (seq_init (funcomp var_term (shift_p Σ'))) a.

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
    apply nth_ext; intros p; rewrite nth_map; cbn.
    rewrite idSubst_term; [reflexivity|].
    intros q; rewrite nth_init; reflexivity.
Qed.

Definition castof {A x y} (P : A -> Type) (e : x = y) (p : P x) : P y :=
match e in _ = y return P y with eq_refl => p end.

Lemma castof_inv : forall A x y P e p,
  castof P (eq_sym e) (@castof A x y P e p) = p.
Proof.
intros.
destruct e; reflexivity.
Qed.

Definition transp {A x y} (P : A -> Type) (e : x = y) : P x -> P y :=
match e in _ = y return P x -> P y with eq_refl => fun v => v end.

Definition extends_cmp : forall Ω Ω' Ω'', extends Ω Ω' -> extends Ω' Ω'' -> extends Ω Ω''.
Proof.
intros Ω Ω' Ω'' α β.
destruct α as [Σ Θ]; destruct β as [Σ' Θ']; cbn in *.
assert (e := eq_sym (PeanoNat.Nat.add_assoc Σ' Σ (idxℙ Ω))).
rewrite List.map_app, List.app_assoc.
set (Θ₀ := (Θ' ++ List.map (nlift_atomic Σ') Θ)%list); clearbody Θ₀; clear Θ Θ'; rename Θ₀ into Θ.
rewrite List.map_map.
match goal with [ |- context [ List.map ?f ?v ] ] =>
  unshelve erewrite (List.map_ext f (transp (fun n => _ -> atomic n) e (fun x => nlift_atomic (Σ' + Σ) x)) _ v)
end.
{ clear; unfold nlift_atomic; intros [a args]; cbn.
  transitivity (existT (fun a => seq (term _) _) a (transp (fun n => seq (term n) _) e (seq_map (subst_term (seq_init (funcomp var_term (shift_p (Σ' + Σ))))) args))).
  2: { destruct e; reflexivity. }
  f_equal; apply nth_ext; intros p.
  rewrite !nth_map, compComp_term, !map_init.
  transitivity (nth ((seq_map (subst_term (seq_init (transp (fun n => _ -> term n) e (funcomp var_term (shift_p (Σ' + Σ)))))) args)) p).
  2: { destruct e; reflexivity. }
  rewrite nth_map; f_equal.
  apply nth_ext; clear p; intro p; rewrite !nth_init.
  unfold funcomp; simpl; rewrite nth_init.
  transitivity (var_term (transp _ e (shift_p (Σ' + Σ) p))).
  2:{ destruct e; reflexivity. }
  f_equal.
  induction Σ'; cbn in *.
  + rewrite (nat_uip _ _ e eq_refl); reflexivity.
  + assert (e' : ((Σ' + Σ) + idxℙ Ω) = (Σ' + (Σ + idxℙ Ω))) by congruence.
    transitivity (shift (transp fin e' (shift_p (Σ' + Σ) p))).
    - f_equal; apply IHΣ'.
    - destruct e'; cbn.
      rewrite (nat_uip _ _ e eq_refl); reflexivity.
}
destruct e; constructor.
Qed.

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

Lemma Forall_of_nth : forall A P (l : list A),
  (forall i : fin (length l), P (nth l i)) -> Forall P l.
Proof.
induction l; intros H; constructor.
+ apply (H None).
+ apply IHl; intros i; apply (H (Some i)).
Defined.

Lemma Forall_to_nth : forall A P (l : list A) (i : fin (length l)),
  Forall P l -> P (nth l i).
Proof.
intros A P l i H; revert i; induction H; intros i; destruct i; simpl; intuition.
Defined.

Definition enrich {Σ} (Ω : ℙ) (ρ : seq (term Ω.(idxℙ)) Σ)
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

Definition lift_fin {Ω Ω'} (e : extends Ω Ω') (p : fin Ω.(idxℙ)) : fin Ω'.(idxℙ) :=
match e in extends _ Ω' return fin Ω'.(idxℙ) with
| Extends _ Σ Θ => shift_p _ p
end.

Definition lift_le {Σ Ω Ω'} (ρ : seq (term Ω.(idxℙ)) Σ) (α : Ω' ≤ Ω) : seq (term Ω'.(idxℙ)) Σ.
Proof.
refine (ρ >> seq_init _).
refine (fun n => var_term (lift_fin (le_to α) n)).
Defined.

Lemma lift_fin_red : forall Σ Ω Φ (α : extends Ω (mkℙ (Σ + idxℙ Ω) Φ)) p,
  lift_fin α p = shift_p Σ p.
Proof.
intros.
refine (
  match α in extends _ Ω' return
    forall (e : idxℙ Ω' = Σ + idxℙ Ω),
    transp fin e (lift_fin α p) = shift_p Σ p
  with
  | Extends _ Σ' Ω' => _
  end eq_refl
).
intros e; simpl in *.
assert (e' : Σ' = Σ) by Lia.lia; destruct e'.
rewrite (nat_uip _ _ e eq_refl); reflexivity.
Qed.

Lemma lift_fin_unique : forall Ω Ω' (α α' : extends Ω Ω') p,
  lift_fin α p = lift_fin α' p.
Proof.
intros Ω Ω' α α' n.
destruct α as [Σα Ωα]; simpl.
rewrite lift_fin_red; reflexivity.
Qed.

Lemma lift_fin_id : forall {Ω} (α : extends Ω Ω) p,
  lift_fin α p = p.
Proof.
intros.
destruct Ω as [Σ Φ]; cbn in *.
rewrite (lift_fin_red 0 _ _ α); reflexivity.
Qed.

Lemma lift_fin_cmp : forall {Ω Ω' Ω''} (α : extends Ω Ω') (β : extends Ω' Ω'') (γ : extends Ω Ω'') p,
  lift_fin γ p = lift_fin β (lift_fin α p).
Proof.
intros.
destruct γ as [Σγ Ωγ]; simpl.
refine (
  match β in extends _ Ω₀ return
    forall (e : idxℙ Ω₀ = Σγ + idxℙ Ω),
    shift_p Σγ p = transp fin e (lift_fin β (lift_fin α p))
  with
  | Extends _ Σβ Ωβ => fun e => _
  end eq_refl
); simpl in *; clear.
refine (
  match α in extends _ Ω₀ return
    forall (e' : idxℙ Ω₀ = _),
    shift_p Σγ p = transp fin e (shift_p Σβ (transp fin e' (lift_fin α p)))
  with
  | Extends _ Σα Ωα => fun e' => _
  end eq_refl
); simpl in *; clear.
destruct e'; cbn.
assert (e' : Σβ + Σα = Σγ).
{ eapply PeanoNat.Nat.add_cancel_r. rewrite <- PeanoNat.Nat.add_assoc; exact e. }
destruct e'.
induction Σβ; cbn in *.
+ rewrite (nat_uip _ _ e eq_refl); reflexivity.
+ assert (e' : (Σβ + (Σα + idxℙ Ω)) = (Σβ + Σα + idxℙ Ω)) by congruence.
  transitivity (shift (transp fin e' (shift_p Σβ (shift_p Σα p)))).
  - f_equal; apply IHΣβ.
  - destruct e'; cbn.
    rewrite (nat_uip _ _ e eq_refl); reflexivity.
Qed.

Lemma lift_le_unique : forall Σ Ω Ω' (ρ : seq (term Ω.(idxℙ)) Σ) (α α' : Ω' ≤ Ω),
  lift_le ρ α = lift_le ρ α'.
Proof.
intros Σ Ω Ω' ρ α α'.
apply nth_ext; intros n; unfold lift_le; cbn.
rewrite !nth_map; f_equal; apply nth_ext; clear n; intro n.
rewrite !nth_init; f_equal.
apply lift_fin_unique.
Qed.

Lemma lift_le_cmp : forall {Σ Ω Ω' Ω''} (ρ : seq (term Ω.(idxℙ)) Σ) (α : Ω' ≤ Ω) (β : Ω'' ≤ Ω'),
  lift_le ρ (β ∘ α) = lift_le (lift_le ρ α) β.
Proof.
intros; apply nth_ext; intros n.
unfold lift_le; rewrite !nth_map, !compComp_term; f_equal.
rewrite !map_init; apply nth_ext; clear n; intro n.
rewrite !nth_init; cbn; rewrite !nth_init; f_equal.
apply lift_fin_cmp.
Qed.

Lemma lift_le_id : forall {Σ Ω} (ρ : seq (term Ω.(idxℙ)) Σ),
  lift_le ρ ! = ρ.
Proof.
intros; apply nth_ext; intros n.
unfold lift_le; simpl.
rewrite nth_map; f_equal.
apply idSubst_term; clear n; intro n.
rewrite nth_init.
rewrite lift_fin_id; reflexivity.
Qed.

Lemma lift_le_nat : forall Σ Σ' Ω Ω' (α : Ω' ≤ Ω)
  (ρ : seq (term (idxℙ Ω)) Σ)
  (σ : seq (term Σ) Σ'),
  (σ >> (lift_le ρ α)) = (lift_le (σ >> ρ) α).
Proof.
intros Σ Σ' Ω Ω' α ρ σ.
apply nth_ext; intros n; rewrite !nth_map.
unfold lift_le; simpl.
rewrite !nth_map.
rewrite compComp_term; reflexivity.
Qed.

Definition InΩ {Σ} Ω (ρ : seq (term Ω.(idxℙ)) Σ) (a : atomic Σ) Ω' (α : Ω' ≤ Ω) :=
 In (subst_atomic (lift_le ρ α) a) Ω'.(ctxℙ).

Lemma In_app_l : forall (A : Type) (l1 l2 : list A) (x : A),
  In x l1 -> In x (app l1 l2).
Proof.
intros A l1 l2 x H; revert l2; induction H; intros l2; simpl; constructor; intuition.
Qed.

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

Lemma In_nth : forall A (l : list A) (i : fin (length l)), In (nth l i) l.
Proof.
induction l; intros i; destruct i; simpl; constructor; intuition.
Qed.

Lemma InΩ_isMon : forall Σ Ω ρ (a : atomic Σ),
  isMon (fun (Ω' : ℙ) (α : Ω' ≤ Ω) => InΩ Ω ρ a Ω' α).
Proof.
intros Σ Ω ρ a Ω' Ω'' α β i.
unfold InΩ in *.
rewrite lift_le_cmp.
assert (β₀ := le_to β); destruct β₀ as [Σ' Θ]; cbn in *.
apply In_app_r.
match goal with [ |- In ?x _ ] =>
  replace x with (nlift_atomic Σ' (subst_atomic (lift_le ρ α) a))
end.
{ apply In_map, i. }
clear i. destruct a as [a args]; cbn in *.
f_equal; apply nth_ext; intros n.
rewrite !nth_map, compComp_term; f_equal.
clear n; apply nth_ext; intros n.
unfold funcomp; cbn.
rewrite nth_map; cbn.
unfold lift_le; rewrite !nth_map, !compComp_term, !map_init.
f_equal; apply nth_ext; intros p; rewrite !nth_init; cbn; rewrite !nth_init; f_equal.
rewrite lift_fin_red; reflexivity.
Qed.

Inductive Dyn (Ω : ℙ) (A : forall Ω', Ω' ≤ Ω -> Type) :=
| ret : A Ω ! -> Dyn Ω A
| ask : forall
  (i : T.(gthy_idx))
  (G := T.(gthy_axm) i)
  (ρ : seq (term Ω.(idxℙ)) G.(geom_ctx)),
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

Fixpoint interp {Σ} (A : form Σ) {Ω : ℙ} (ρ : seq (term Ω.(idxℙ)) Σ) {struct A} : Type := 
match A with
| Atm a args => Dyn Ω (fun Ω' α => InΩ Ω ρ (existT _ a args) Ω' α)
| Arr A B =>
  forall Ω' (α : Ω' ≤ Ω), interp A (lift_le ρ α) -> interp B (lift_le ρ α)
| Top => True
| Bot => Dyn Ω (fun Ω' α => False)
| Cnj A B => prod (interp A ρ) (interp B ρ)
| Dsj A B => Dyn Ω (fun Ω' α => interp A (lift_le ρ α) + interp B (lift_le ρ α))%type
| All A =>
  forall Ω' (α : Ω' ≤ Ω) (t : term Ω'.(idxℙ)), interp A (scons t (lift_le ρ α))
| Exs A =>
  Dyn Ω (fun Ω' α => { t : term Ω'.(idxℙ) & interp A (scons t (lift_le ρ α)) })
end.

Definition iffT (A B : Type) := prod (A -> B) (B -> A).

Lemma interp_subst : forall Σ Σ' (A : form Σ') Ω (ρ : seq (term Ω.(idxℙ)) Σ) σ,
  iffT (interp (subst_form σ A) ρ) (interp A (σ >> ρ)).
Proof.
intros Σ Σ' A; revert Σ; induction A; intros Σ Ω ρ σ; split; cbn in *.
+ refine (Dyn_map _).
  unfold InΩ; intros Ω' α i; cbn in *.
  match goal with [ H : In (existT _ a ?p) _ |- In (existT _ a ?q) _ ] => replace q with p; [assumption|] end.
  apply nth_ext; intros n; simpl; rewrite !nth_map.
  rewrite <- lift_le_nat, compComp_term; reflexivity.
+ refine (Dyn_map _).
  unfold InΩ; intros Ω' α i; cbn in *.
  match goal with [ H : In (existT _ a ?p) _ |- In (existT _ a ?q) _ ] => replace q with p; [assumption|] end.
  apply nth_ext; intros n; simpl; rewrite !nth_map.
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
  apply nth_ext; intros [n|]; simpl in *; [|reflexivity].
  rewrite !nth_map, compComp_term, map_init_eta; reflexivity.
+ intros f Ω' α t.
  specialize (f Ω' α t).
  apply IHA.
  rewrite <- lift_le_nat in f.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  apply nth_ext; intros [n|]; simpl; [|reflexivity].
  rewrite !nth_map, compComp_term, map_init_eta; reflexivity.
+ refine (Dyn_map _); intros Ω' α [t p]; exists t.
  apply IHA in p.
  rewrite <- lift_le_nat.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  apply nth_ext; intros [n|]; simpl; [|reflexivity].
  rewrite !nth_map, compComp_term, map_init_eta; reflexivity.
+ refine (Dyn_map _); intros Ω' α [t p]; exists t.
  apply IHA.
  rewrite <- lift_le_nat in p.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.
  set (τ := lift_le ρ α); clearbody τ; clear - T.
  apply nth_ext; intros [n|]; simpl; [|reflexivity].
  rewrite !nth_map, compComp_term, map_init_eta; reflexivity.
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
+ match type of x with Dyn _ ?A =>
  unshelve refine (let x := Dyn_isMon _ A _ _ _ ! α x in _); [|clearbody x; cbn in x]
  end.
  { clear - IHA; intros Ω' Ω'' α β [t Ht].
    apply (IHA _ _ β) in Ht.
    exists (subst_term (lift_le (seq_init var_term) β) t).
    match goal with [ H : interp A ?t |- interp A ?u ] =>
      replace u with t; [exact H|]
    end.
    simpl; f_equal; [f_equal|rewrite lift_le_cmp; reflexivity].
    apply nth_ext; intro n; unfold lift_le; rewrite !nth_map, !nth_init; simpl; rewrite nth_init.
    reflexivity.
  }
  refine (Dyn_map (fun Ω'' β  => _) x).
  intros [t Ht]; exists t.
  rewrite <- lift_le_cmp.
  replace (lift_le ρ (β ∘ α)) with (lift_le ρ (β ∘ (α ∘ !))) by apply lift_le_unique.
  assumption.
Qed.

Lemma interp_alg {Σ} (A : form Σ) {Ω} ρ
  (x : Dyn Ω (fun Ω' α => interp A (lift_le ρ α))) : interp A ρ.
Proof.
revert Ω ρ x; induction A; intros Ω ρ p; cbn in *.
+ refine (Dyn_bind p (fun Ω' α x => _)); cbn in *.
  refine (Dyn_map (fun Ω'' β x => _) x); cbn in *.
  unfold InΩ in *.
  rewrite lift_le_cmp; assumption.
+ intros Ω' α x.
  apply IHA2.
  match type of p with Dyn _ ?A => unshelve refine (Dyn_bind (Dyn_isMon _ A _ _ _ ! α p) _) end.
  { apply (interp_isMon _ (Arr A1 A2)). }
  cbn. intros Ω'' β f; apply ret.
  specialize (f Ω'' !).
  rewrite <- lift_le_cmp.
  replace ((! ∘ β) ∘ α)  with (! ∘ (β ∘ (α ∘ !))) by reflexivity.
  rewrite lift_le_cmp; apply f.
  assert (x' := interp_isMon _ A1 _ _ _ _ _ β x); cbn in x'.
  rewrite <- lift_le_cmp.
  exact x'.
+ constructor.
+ refine (Dyn_bind p (fun _ _ x => x)).
+ split.
  - apply IHA1.
    refine (Dyn_map (fun Ω'' β => _) p); intros [x _]; assumption.
  - apply IHA2.
    refine (Dyn_map (fun Ω'' β => _) p); intros [_ y]; assumption.
+ refine (Dyn_bind p (fun Ω' α x => _)).
  refine (Dyn_map (fun Ω'' β => _) x).
  intros [l|r]; [left|right]; rewrite lift_le_cmp; assumption.
+ intros Ω' α t.
  apply IHA.
  match type of p with Dyn _ ?A => unshelve refine (Dyn_bind (Dyn_isMon _ A _ _ _ ! α p) _) end.
  { apply (interp_isMon _ (All A)). }
  intros Ω'' β x; apply ret.
  specialize (x _ ! (subst_term (lift_le (seq_init var_term) β) t)).
  match goal with [ _ : interp A ?t |- interp A ?u ] => replace u with t end; [assumption|].
  apply nth_ext; intros [n|]; cbn.
  - rewrite !lift_le_id.
    change (β ∘ (α ∘ !)) with (β ∘ α).
    rewrite lift_le_cmp.
    reflexivity.
  - f_equal.
    unfold lift_le; apply nth_ext; intros n; rewrite !map_init, !nth_init; simpl; rewrite !nth_init.
    reflexivity.
+ refine (Dyn_bind p (fun Ω' α p => _)); cbn in *.
  refine (Dyn_map (fun Ω'' β p => _) p); cbn in *.
  destruct p as [t Ht]; exists t.
  rewrite lift_le_cmp; assumption.
Qed.

Lemma interp_nAll : forall Σ (A : form Σ) Ω (ρ : seq (term Ω.(idxℙ)) 0),
  (forall Ω' (α : Ω' ≤ Ω) σ, @interp Σ A Ω' σ) -> interp (nAll Σ A) ρ.
Proof.
induction Σ as [|Σ IHΣ]; intros A Ω ρ p; cbn.
+ specialize (p Ω !); apply p.
+ apply IHΣ; intros Ω' α σ; cbn; intros Ω'' β t.
  apply p, (β ∘ α).
Defined.

Lemma interp_nSplit : forall Σ Ψ Ω (ρ : seq (term Ω.(idxℙ)) Σ) (o : fin (length Ψ)),
  match nth Ψ o with existT _ Σ' Φ => { σ : _ & @interp _ (nCnj Φ) Ω (scons_p σ ρ) } end ->
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
    { revert Σ ρ Φ p. induction σ; intros Σ ρ Φ p; cbn in *.
      + assumption.
      + apply IHσ.
        cbn; apply ret; exists a.
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

Lemma interp_nCnj_of : forall Σ (Φ : list (atomic Σ)) Ω (ρ : seq (term Ω.(idxℙ)) Σ),
  interp (nCnj Φ) ρ ->
  Dyn Ω (fun Ω' α => Forall (fun φ => In (subst_atomic (lift_le ρ α) φ) Ω'.(ctxℙ)) Φ).
Proof.
intros Σ Φ; induction Φ as [|[a args] Φ IHΦ]; intros Ω ρ p; cbn in *.
+ apply ret; constructor.
+ destruct p as [x p]; cbn in *.
  apply IHΦ in p.
  refine (Dyn_bind p _); clear p; intros Ω' α p.
  unshelve refine (Dyn_bind (Dyn_isMon _ _ _ _ _ ! α x) _); clear x.
  { apply InΩ_isMon. }
  intros Ω'' β x; apply ret; constructor.
  - apply x.
  - simple refine (Forall_map _ _ p).
    cbn; clear - T; intros a.
    intros H.
    apply InΩ_isMon, H.
Qed.

Lemma interp_nCnj_to : forall Σ (Φ : list (atomic Σ)) Ω (ρ : seq (term Ω.(idxℙ)) Σ),
  Forall (fun φ => In (subst_atomic ρ φ) Ω.(ctxℙ)) Φ -> interp (nCnj Φ) ρ.
Proof.
intros Σ Φ Ω ρ H; induction H; constructor; simpl in *.
+ destruct x as [a args]; simpl in *.
  apply ret; unfold InΩ; rewrite lift_le_id; apply p.
+ assumption.
Qed.

Lemma interp_geometric_axiom :
  forall (i : gthy_idx T) (Ω : ℙ) (ρ : seq (term (idxℙ Ω)) 0),
    interp (of_geometric (gthy_axm T i)) ρ.
Proof.
intros i Ω ρ.
set (φ := gthy_axm T i).
unfold of_geometric.
apply interp_nAll; intros Ω' α σ; cbn; intros Ω'' β H.
apply interp_alg.
apply interp_nCnj_of in H.
refine (Dyn_bind H _); clear H; intros Ω''' γ H.
unshelve refine (ask _ _ i (lift_le σ (γ ∘ β)) _ _); fold φ.
- set (Φ := geom_hyp φ) in *; clearbody Φ;
  set (Σ' := geom_ctx φ) in *; clearbody Σ'; clear - H.
  apply Forall_of_nth; intros i Ω'''' δ.
  apply (Forall_to_nth _ _ _ i) in H; simpl in H.
  rewrite <- lift_le_cmp in H.
  refine (InΩ_isMon _ _ _ _ _ _ ! _ _).
  unfold InΩ; rewrite lift_le_id; exact H.
- intros o ψ Ω'''' δ.
  apply ret; apply interp_nSplit with o.
  fold ψ; destruct ψ as [Σ' Φ]; cbn.
  rewrite <- !lift_le_cmp.
  match goal with [ |- context [ scons_p _ (lift_le _ ?α) ] ] => set (υ := α); clearbody υ end.
  exists (seq_init (fun p => var_term (zero_p _ p))).
  apply interp_nCnj_to; apply Forall_of_nth; intros j.
  unfold enrich; simpl.
  apply In_app_l.
  erewrite List.map_ext; [now apply In_map, In_nth|].
  clear; intros [a args]; simpl; f_equal.
  apply nth_ext; intros p; rewrite !nth_map; f_equal.
  unfold upList_term_term; f_equal.
  apply nth_ext; clear p; intros p; rewrite !nth_map; f_equal.
  unfold lift_le; rewrite !nth_map, !compComp_term; f_equal.
  apply nth_ext; clear p; intro p; rewrite !nth_map, !nth_init; simpl.
  rewrite !nth_init; unfold funcomp; f_equal.
  unfold enrich in υ; simpl in υ; simpl in *; clear.
  revert υ.
  set (α₀ := (δ ∘ (γ ∘ β))); clearbody α₀; clear; rename α₀ into α; intros υ.
  let Ω₀ := match type of υ with ?Ω ≤ _ => Ω end in
  assert (β : Ω₀ ≤ Ω'''').
  { apply le_of; constructor. }
  rewrite (lift_fin_unique _ _ (le_to υ) (le_to (β ∘ α))); clear υ.
  rewrite (lift_fin_cmp (le_to α) (le_to β) (le_to (β ∘ α))).
  rewrite lift_fin_red; reflexivity.
Qed.

Lemma interp_sound : forall Σ Γ (A : form Σ) Ω (ρ : seq (term Ω.(idxℙ)) Σ),
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
  rewrite map_init_eta.
  unshelve refine (interp_isMon _ _ _ _ _ _ ! _ _).
  rewrite lift_le_id.
  assumption.
+ specialize (IHπ Ω ρ γ Ω ! (subst_term ρ t)).
  apply interp_subst.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.  
  rewrite lift_le_id.
  apply nth_ext; intros [n|]; [|reflexivity].
  simpl; rewrite nth_map, nth_init; reflexivity.
+ apply ret.
  exists (subst_term ρ t).
  specialize (IHπ Ω ρ γ).
  apply interp_subst in IHπ.
  match goal with [ H : interp A ?σ |- interp A ?τ ] => replace τ with σ; [assumption|] end.  
  rewrite lift_le_id.
  apply nth_ext; intros [n|]; [|reflexivity].
  simpl; rewrite nth_map, nth_init; reflexivity.
+ specialize (IHπ1 _ _ γ).
  apply interp_alg.
  refine (Dyn_map _ IHπ1); intros Ω' α [t p].
  specialize (IHπ2 Ω' (scons t (lift_le ρ α))).
  simple refine (let IHπ2 := IHπ2 _ in _); [|clearbody IHπ2].
  { apply Forall_map_nat.
    refine (Forall_map _ _ γ).
    clear. intros X x.
    apply interp_subst; rewrite map_init_eta.
    unshelve refine (interp_isMon _ _ _ _ _ _ ! _ _).
    rewrite lift_le_id; assumption.
  }
  apply interp_subst in IHπ2.
  match goal with [ H : interp B ?σ |- interp B ?τ ] => replace τ with σ; [assumption|] end.
  clear; apply nth_ext; intro n; unfold lift_le; rewrite !map_init, !nth_map, !nth_init; simpl.
  rewrite nth_map; reflexivity.
Qed.

End Interp.

End Dynamic.
