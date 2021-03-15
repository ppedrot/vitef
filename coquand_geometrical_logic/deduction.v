Require List Eqdep_dec Lia.
Require Import seq syntax.

Lemma nat_uip : forall (m n : nat) (p q : m = n), p = q.
Proof.
intros; apply Eqdep_dec.UIP_dec.
decide equality.
Qed.

Set Primitive Projections.

Section syntax.

Context {Sig : sig}.
Notation form := (@form Sig).

Record Theory := {
  thy_idx : Set;
  thy_axm : forall i : thy_idx, form 0;
}.

Inductive In {A} (x : A) : list A -> Type :=
| In_here : forall l, In x (cons x l) 
| In_next : forall y l, In x l -> In x (cons y l).

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

Lemma map_init_eta : forall Σ Σ' t (ρ : seq (@term Sig Σ) Σ'),
  init (funcomp var_term shift) >> scons t ρ = ρ.
Proof.
intros.
rewrite map_init; apply nth_ext; intros n.
rewrite nth_init; reflexivity.
Qed.

End syntax.
