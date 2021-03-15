Require Import seq syntax deduction.

Section Std.

Context {Sig : sig}.
Hypothesis Sig_intuitionistic : Sig.(sig_classical) = false.

Notation symb := Sig.(sig_symb).
Notation symb_arity := Sig.(sig_symb_arity).
Notation atom := Sig.(sig_atom).
Notation atom_arity := Sig.(sig_atom_arity).
Notation term := (@term Sig).


Definition env (Σ : nat) := seq (term 0) Σ.
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

Variable T : @Theory Sig.

Variable T_sound : forall (i : T.(thy_idx)), interp null (T.(thy_axm) i).

Lemma interp_sound : forall Σ (ρ : env Σ) Γ (A : form Σ) (π : proof T Σ Γ A),
  List.Forall (fun A => interp ρ A) Γ -> interp ρ A.
Proof.
induction 1; intros γ; cbn.
+ exfalso; congruence.
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
  rewrite (@map_init_eta Sig); reflexivity.
+ cbn in IHπ.
  apply interp_subst; simpl.
  specialize (IHπ ρ γ (subst_term ρ t)).
  match goal with [ |- interp ?s _ ] => replace s with (scons (subst_term ρ t) ρ); [assumption|] end.
  apply nth_ext; intros [m|]; simpl; [|reflexivity].
  rewrite varL_term; reflexivity.
+ exists (subst_term ρ t).
  specialize (IHπ ρ γ).
  apply interp_subst in IHπ.
  match goal with [ |- interp ?s _ ] => replace s with ((scons t (init var_term)) >> ρ); [assumption|] end.
  apply nth_ext; intros [m|]; simpl; [|reflexivity].
  rewrite varL_term; reflexivity.
+ specialize (IHπ1 ρ γ); destruct IHπ1 as [t Ht].
  specialize (IHπ2 (scons t ρ)).
  match type of IHπ2 with ?T -> _ => assert T end.
  { clear - γ; induction γ; cbn in *; constructor.
    - unfold lift_form.
      apply interp_subst; cbn.
      rewrite (@map_init_eta Sig); apply H.
    - intuition.
  }
  specialize (IHπ2 H).
  unfold lift_form in IHπ2; apply interp_subst in IHπ2.
  rewrite (@map_init_eta Sig) in IHπ2; apply IHπ2.
Qed.

Lemma proof_consistent : proof T 0 nil Bot -> False.
Proof.
intros π.
refine (interp_sound _ null _ _ π _).
constructor.
Qed.

End Std.
