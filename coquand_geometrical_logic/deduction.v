Require List Eqdep_dec Lia.
Require Import seq syntax.

(* Nothing to do here, move me *)

Lemma nat_uip : forall (m n : nat) (p q : m = n), p = q.
Proof.
intros; apply Eqdep_dec.UIP_dec.
decide equality.
Qed.

Inductive In {A} (x : A) : list A -> Type :=
| In_here : forall l, In x (cons x l)
| In_next : forall y l, In x l -> In x (cons y l).

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

Lemma In_map_rev : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (List.map f l) -> {x : A & prod (In x l) (y = f x)}.
Proof.
intros A B f l y H; induction l as [|x l IHl]; cbn in *; inversion H; subst.
+ repeat econstructor.
+ destruct IHl as [x' [? ?]]; [assumption|].
  exists x'; repeat constructor; assumption.
Qed.

Set Primitive Projections.

Section syntax.

Context {Sig : sig}.
Notation form := (@form Sig).

Record Theory := {
  thy_idx : Type;
  thy_axm : forall i : thy_idx, form 0;
}.

Definition lift_form {Σ : nat} (A : form Σ) : form (S Σ) :=
  subst_form (init (fun n => @var_term _ (S _) (Some n))) A.

Inductive proof (T : Theory) (Σ : nat) (Γ : list (form Σ)) : form Σ -> Type :=
| prf_exm :
  forall A, Sig.(sig_classical) = true -> proof T Σ Γ (Dsj A (Arr A Bot))
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
| prf_dsj_i₁ : forall A B,
  proof T Σ Γ A -> proof T Σ Γ (Dsj A B)
| prf_dsj_i₂ : forall A B,
  proof T Σ Γ B -> proof T Σ Γ (Dsj A B)
| prf_dsj_e : forall A B C,
  proof T Σ Γ (Dsj A B) -> proof T Σ (cons A Γ) C -> proof T Σ (cons B Γ) C -> proof T Σ Γ C
| prf_frl_i :
  forall (A : form (S Σ)), proof T (S Σ) (List.map lift_form Γ) A -> proof T Σ Γ (All A) 
| prf_frl_e :
  forall (A : form (S Σ)) (t : term Σ), proof T Σ Γ (All A) ->
  proof T Σ Γ (subst_form (scons t (init var_term)) A)
| prf_exs_i :
  forall (A : form (S Σ)) (t : term Σ),
  proof T Σ Γ (subst_form (scons t (init var_term)) A) -> proof T Σ Γ (Exs A)
| prf_exs_e :
  forall (A : form (S Σ)) (B : form Σ),
  proof T Σ Γ (Exs A) ->
  proof T (S Σ) (List.map lift_form Γ) (lift_form B) ->
  proof T Σ Γ B
.

(* Derived rules *)

Lemma prf_wkn : forall T Σ Γ Δ A, (forall X, In X Γ -> In X Δ) -> proof T Σ Γ A -> proof T Σ Δ A.
Proof.
intros T Σ Γ Δ A Hi H; revert Δ Hi; induction H; intros Δ Hi; try (solve [econstructor; eauto]).
+ apply prf_arr_i, IHproof.
  { intros X HX; inversion HX; subst; constructor; now intuition. }
+ eapply prf_dsj_e; [apply IHproof1, Hi|apply IHproof2|apply IHproof3].
  all: intros X HX; inversion HX; subst; constructor; now intuition.
+ apply prf_frl_i, IHproof.
  { intros X HX. apply In_map_rev in HX; destruct HX as [Y [HY ->]].
    apply In_map, Hi, HY. }
+ eapply prf_exs_e; [apply IHproof1, Hi|apply IHproof2].
  { intros X HX. apply In_map_rev in HX; destruct HX as [Y [HY ->]].
    apply In_map, Hi, HY. }
Qed.

Lemma prf_subst : forall T Σ Σ' Γ A (ρ : seq (term Σ') Σ),
  proof T Σ Γ A -> proof T Σ' (List.map (subst_form ρ) Γ) (subst_form ρ A).
Proof.
intros T Σ Σ' Γ A ρ p; revert Σ' ρ; induction p; intros Σ' ρ; try (solve [econstructor; eauto]).
+ rewrite compComp_form.
  apply prf_thy.
+ apply prf_axm, In_map; assumption.
+ cbn; apply prf_frl_i.
  specialize (IHp (S Σ') (up_term_term ρ)).
  match goal with [ _ : proof _ _ ?Γ _ |- proof _ _ ?Δ _ ] => replace Δ with Γ; [assumption|] end.
  rewrite !List.map_map; apply List.map_ext; clear; intros A.
  unfold lift_form; rewrite !compComp_form.
  f_equal; apply nth_ext; intros n.
  rewrite !nth_map, !nth_init; cbn.
  rewrite !nth_map; reflexivity.
+ cbn in *.
  rewrite compComp_form; simpl.
  specialize (IHp Σ' ρ).
  eapply prf_frl_e with (t := subst_term ρ t) in IHp.
  match goal with [ _ : proof _ _ _ ?A |- proof _ _ _ ?B ] => replace B with A; [assumption|] end.
  rewrite compComp_form; f_equal; simpl; f_equal.
  apply nth_ext; clear; intros n; rewrite !nth_map, !compComp_term, !nth_init; simpl.
  apply idSubst_term; clear; intros m; rewrite !nth_map, !nth_init; simpl; rewrite nth_init; reflexivity.
+ cbn in *; eapply prf_exs_i with (t := subst_term ρ t).
  specialize (IHp Σ' ρ).
  match goal with [ _ : proof _ _ _ ?A |- proof _ _ _ ?B ] => replace B with A; [assumption|] end.
  rewrite !compComp_form; f_equal; apply nth_ext; clear; intros [n|]; [|reflexivity].
  simpl; rewrite !nth_map, !compComp_term, !map_init; simpl.
  rewrite idSubst_term.
  2:{ clear; intros n; rewrite !nth_init; reflexivity. }
  rewrite nth_init; reflexivity.
+ cbn in *. specialize (IHp1 Σ' ρ).
  eapply prf_exs_e in IHp1; [now apply IHp1|].
  specialize (IHp2 (S Σ') (up_term_term ρ)).
  assert (e : forall A, subst_form (up_term_term ρ) (lift_form A) = lift_form (subst_form ρ A)).
  { clear; intros A; unfold up_term_term, lift_form.
    rewrite !compComp_form; f_equal; apply nth_ext; intros n.
    rewrite !nth_map, !nth_init; simpl; rewrite !nth_map; reflexivity. }
  match goal with [ _ : proof _ _ ?Γ ?A |- proof _ _ ?Δ ?B ] =>
    replace Δ with Γ; [replace B with A|]; [assumption| |]
  end.
  - rewrite e; reflexivity.
  - rewrite !List.map_map; apply List.map_ext; intros ?; apply e.
Qed.

End syntax.
