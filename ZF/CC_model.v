Require PTS_type_eq.
Require Import Morphisms Base Cartesian.

Module Sorts <: PTS_base.term_sig.

Inductive sorts := set | kind.

Definition Sorts := sorts.

End Sorts.

Module Axioms <: PTS_base.pts_sig (Sorts).

Import Sorts.

Inductive ax : sorts -> sorts -> Prop :=
  ax_constr : ax set kind.

Definition Ax := ax.

Inductive rel : sorts -> sorts -> sorts -> Prop :=
| rel_lam : rel set set set
| rel_F : rel kind set set
| rel_dep : rel set kind kind
| rel_ho : rel kind kind kind.

Definition Rel := rel.

End Axioms.

Declare Module Term : PTS_term.ut_term_mod Sorts.
Declare Module Env : PTS_env.ut_env_mod Sorts Term.
Declare Module Red : PTS_red.ut_red_mod Sorts Term.
Declare Module SR : PTS_sr.ut_sr_mod Sorts Axioms Term Env Red.
Declare Module CC : PTS_type_eq.ut_typ_eq_mod Sorts Axioms Term Env Red SR.

Import Sorts Axioms.

(* Record function_def (x y f : V) : Prop :={
  function_def_def : forall u : V, u ∈ x -> ;
}. *)

Definition app f x :=
  comprehension (union (union f)) (fun α => tuple x α ∈ f).

Definition reify (A : V) (f : V -> V) : V :=
  comprehension (product A (union (collection A f)))
  (fun p => exists x, exists α, α ∈ f x /\ p ≅ tuple x α).

Definition dsum (A : V) (B : V) : V :=
  comprehension (product A (union (union B)))
  (fun p => exists x, exists y, x ∈ A /\ y ∈ app B x /\ p ≅ tuple x y).

Definition dprd (A : V) (B : V) : V :=
  comprehension (powerset (dsum A B))
  (fun f => function_def A (collection A (app B)) f).

Instance Proper_app : Proper (V_eq ==> V_eq ==> V_eq) app.
Proof.
intros x1 x2 Hx y1 y2 Hy; unfold app; f_equiv.
+ rewrite Hx; reflexivity.
+ intros z1 z2 Hz; rewrite Hx, Hy, Hz; reflexivity.
Qed.

Instance Proper_reify : Proper (V_eq ==> (V_eq ==> V_eq) ==> V_eq) reify.
Proof.
intros x1 x2 Hx f1 f2 Hf; unfold reify; f_equiv.
+ f_equiv; [assumption|].
  f_equiv; f_equiv; [assumption|assumption].
+ intros y1 y2 Hy; f_equiv; intros x; f_equiv; intros α; f_equiv.
  - f_equiv; apply Hf; reflexivity.
  - split; rewrite Hy; tauto.
Qed.

Lemma dsum_spec : forall A B p,
  p ∈ dsum A B <-> (exists x, exists y, x ∈ A /\ y ∈ app B x /\ p ≅ tuple x y).
Proof.
intros A B p.
assert (HP : Proper (V_eq ==> iff) (fun p0 : V => exists x y : V, x ∈ A /\ y ∈ app B x /\ p0 ≅ tuple x y)).
{ intros x1 x2 Hx; f_equiv; intros x; f_equiv; intros y.
  do 2 f_equiv; split; rewrite Hx; trivial. }
split; intros H.
+ apply comprehension_spec in H; [|assumption].
  destruct H as [Hp [x [y [Hx [Hy Heq]]]]].
  exists x, y; intuition.
+ destruct H as [x [y [Hx [Hy Heq]]]].
  apply comprehension_spec; [assumption|].
  split; [|exists x, y; split; [|split]; first [assumption|reflexivity]].
  apply product_spec; exists x, y.
  split; [assumption|]; split; [|assumption]; clear p Heq.
  apply comprehension_spec in Hy; [|intros z1 z2 Hz; rewrite Hz; reflexivity].
  now intuition.
Qed.

Lemma reify_spec : forall A f x, Proper (V_eq ==> V_eq) f ->
  x ∈ A -> app (reify A f) x ≅ f x.
Proof.
intros A f x Hf Hx.
assert (HP : Proper (V_eq ==> iff) (fun p : V => exists x α : V, α ∈ f x /\ p ≅ tuple x α)).
{ clear - Hf; intros p1 p2 Hp; f_equiv; intros x; f_equiv; intros α.
  f_equiv; split; rewrite Hp; tauto. }
apply extensionality; apply included_spec; intros z Hz.
+ apply comprehension_spec in Hz.
  - destruct Hz as [Hz Hi].
    apply union_spec in Hz; destruct Hz as [r [Hz Hr]].
    apply union_spec in Hr; destruct Hr as [s [Hr Hs]].
    apply comprehension_spec in Hi; [|assumption].
    destruct Hi as [Hi [u [α [Hp Ht]]]].
    assert (Hrw := tuple_inj_l _ _ _ _ Ht); rewrite Hrw in *; clear x Hrw.
    assert (Hrw := tuple_inj_r _ _ _ _ Ht); rewrite Hrw in *; assumption.
  - clear - Hf; intros x1 x2 Hx; rewrite Hx; reflexivity.
+ apply comprehension_spec.
  - clear - Hf; intros x1 x2 Hx; rewrite Hx; reflexivity.
  - assert (Hm : tuple x z ∈ reify A f).
    { apply comprehension_spec; [exact HP|].
      split; [|exists x, z; split; [assumption|reflexivity]].
      apply product_spec; exists x, z.
      split; [assumption|]; split; [|reflexivity].
      apply union_spec; exists (f x); split; [assumption|].
      apply collection_spec; [exact Hf|].
      exists x; split; [assumption|reflexivity]. }
    split; [|assumption].
    apply union_spec; exists (pair x z).
    split; [apply pair_spec; right; reflexivity|].
    apply union_spec; exists (tuple x z).
    split; [apply pair_spec; right; reflexivity|].
    assumption.
Qed.

Lemma reify_impredicative : forall A, reify A (fun _ => empty) ≅ empty.
Proof.
intros A; apply extensionality; apply included_spec; intros x Hx.
+ exfalso; apply comprehension_spec in Hx.
  - destruct Hx as [Hx [p [α [Hα Hp]]]].
    apply empty_spec in Hα; contradiction.
  - clear; intros x1 x2 Hx; f_equiv; intros x; f_equiv; intros α.
    split; rewrite Hx; auto.
+ apply empty_spec in Hx; contradiction.
Qed.

Lemma app_empty : forall x, app empty x ≅ empty.
Proof.
intros x.
pose (Hrw := reify_impredicative (singleton x)).
rewrite <- Hrw at 1; rewrite reify_spec.
+ reflexivity.
+ intros _ _ _; reflexivity.
+ apply singleton_spec; reflexivity.
Qed.

Program Fixpoint term_eval (Γ : Env.Env) (M : Term.Term) {struct M} : V :=
match M with
| Term.Var n => empty
| Term.Sort set => powerset (singleton empty)
| Term.Sort kind => empty
| Term.App M N => app (term_eval Γ M) (term_eval Γ N)
| Term.Pi A B => dprd (term_eval Γ A) (term_eval (cons A Γ) B)
| Term.La A M => reify (term_eval Γ A) (fun x => term_eval (cons A Γ) M)
end.

Lemma term_eval_type_eq_compat : forall Γ M1 M2 A, CC.typ_eq Γ M1 M2 A ->
  term_eval Γ M1 ≅ term_eval Γ M2
with term_eval_type_compat : forall Γ M A, CC.typ Γ M A ->
  term_eval Γ M ∈ term_eval Γ A.
Proof.
{ intros Γ M1 M2 A HR; induction HR; simpl; try solve [f_equiv; assumption].
  + admit.
  + f_equiv; [assumption|]; intros _ _ _.
    admit.
  + symmetry; assumption.
  + etransitivity; eassumption.
  + assumption.
  + rewrite reify_spec; [|intros _ _ _; reflexivity|].
    admit.
Admitted.
