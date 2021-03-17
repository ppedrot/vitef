Require Import seq syntax deduction.

Set Primitive Projections.

Section geometric.

Context {Sig : sig}.

Notation symb := Sig.(sig_symb).
Notation symb_arity := Sig.(sig_symb_arity).
Notation atom := Sig.(sig_atom).
Notation atom_arity := Sig.(sig_atom_arity).
Notation term := (@term Sig).
Notation form := (@form Sig).

Definition atomic Σ := { a : atom & seq (term Σ) (atom_arity a) }.

Definition subst_atomic {Σ Σ' : nat} (σ : seq (term Σ') Σ) (a : atomic Σ) : atomic Σ' :=
match a with
| existT _ α args => existT _ α (args >> σ)
end.

Definition nlift_atomic {Σ} Σ' (a : atomic Σ) : atomic (Σ' + Σ) :=
  subst_atomic (init (funcomp var_term (shift_p Σ'))) a.

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
  gthy_idx : Type;
  gthy_axm : forall (i : gthy_idx), geometric;
}.

Definition of_gtheory (T : GTheory) : Theory := {|
  thy_idx := T.(gthy_idx);
  thy_axm := fun i => of_geometric (T.(gthy_axm) i);
|}.

End geometric.

Coercion of_gtheory : GTheory >-> Theory.
