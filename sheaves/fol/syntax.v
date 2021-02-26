Require Import seq.

Notation var_zero := fin0.
Notation shift := finS.
Notation null := seq0.
Notation scons := seqS.
Notation scons_p := seq_app.

Axiom symb : Set.
Axiom symb_arity : symb -> nat.
Axiom atom : Set.
Axiom atom_arity : atom -> nat.

Section term.

Unset Elimination Schemes.
Inductive term (nterm : nat) : Type :=
| var_term : fin nterm -> term nterm
| App : forall (s : symb) (l : seq (term (nterm)) (symb_arity s)), term (nterm).
Set Elimination Schemes.

Lemma term_rect : forall (n : nat) (P : term n -> Type)
  (pvar : forall f : fin n, P (var_term n f))
  (papp : forall (s : symb) (l : seq (term n) (symb_arity s)), (forall p, P (nth l p)) -> P (App n s l)),
  forall t : term n, P t.
Proof.
intros n P pvar papp.
simple refine (
fix F t :=
match t return P t with
| var_term _ p => pvar _
| App _ s l => papp _ _ (fun p => _)
end 
).
refine (
(fix G (m : nat) (l : seq (term n) m) {struct l} : forall (p : fin m), P (nth l p) :=
match l in seq _ m return forall p : fin m, P (nth l p) with
| seq0 => fun p => match p with end
| seqS x l =>
  fun p => match p return (forall p, P (nth l p)) -> P (nth (seqS x l) p) with
  | None => fun _ => F x
  | Some p => fun G => G p
  end (G _ l)
end
) _ l p).
Defined.

Definition term_ind (n : nat) (P : term n -> Type)
  (pvar : forall f : fin n, P (var_term n f))
  (papp : forall (s : symb) (l : seq (term n) (symb_arity s)), (forall p, P (nth l p)) -> P (App n s l))
  (t : term n) : P t :=
  term_rect n P pvar papp t.

Fixpoint subst_term { mterm : nat } { nterm : nat } (sigmaterm : seq (term (nterm)) mterm)  (s : term (mterm)) {struct s} : term (nterm) :=
match s with
| var_term (_) s => nth sigmaterm s
| App (_) s s0 => App (nterm) s (seq_map (subst_term sigmaterm) s0)
end.

Definition funcomp {A B C} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

Definition up_term_term { m : nat } { nterm : nat } (sigma : seq (term nterm) m) : seq (term (S nterm)) (S m).
Proof.
simple refine (seqS ((var_term (S nterm)) (var_zero)) _).
simple refine (seq_map (subst_term _) sigma).
refine (seq_init (funcomp (var_term _) shift)).
Defined.

Definition upList_term_term (p : nat) { m : nat } { nterm : nat } (sigma : seq (term (nterm)) m) : seq (term (p+ nterm)) (p + m).
Proof.
simple refine (scons_p _ _).
+ refine (seq_init (((funcomp) (var_term (p+ nterm)) (zero_p p)))).
+ refine (seq_map _ sigma).
  refine ((subst_term (seq_init ((funcomp) (var_term (_)) (shift_p p))))).
Defined.

Definition upId_term_term { mterm : nat }
  (sigma : seq (term (mterm)) mterm)
  (Eq : forall x, nth sigma x = (var_term (mterm)) x) :
  forall x, nth (up_term_term sigma) x = (var_term ((S) mterm)) x.
Proof.
intros [n|]; [|reflexivity].
unfold up_term_term; cbn.
rewrite nth_map; cbn.
rewrite Eq; cbn; rewrite nth_init; cbn; reflexivity.
Qed.

Definition upIdList_term_term { p : nat } { mterm : nat }
  (sigma : seq (term mterm) mterm)
  (Eq : forall x, nth sigma x = (var_term (mterm)) x) :
  forall x, nth (upList_term_term p sigma) x = (var_term (p + mterm)) x.
Proof.
apply fin_add_rect; intros n; unfold upList_term_term; cbn.
+ rewrite nth_zero_p; cbn.
  rewrite nth_init; reflexivity.
+ rewrite nth_shift_p; cbn.
  rewrite nth_map, Eq; cbn.
  rewrite nth_init; reflexivity.
Qed.

Fixpoint idSubst_term { mterm : nat }
  (sigmaterm : seq (term mterm) mterm)
  (Eqterm : forall x, nth sigmaterm x = (var_term (mterm)) x)
  (s : term (mterm)) : subst_term sigmaterm s = s.
Proof.
induction s.
+ apply Eqterm.
+ cbn; f_equal; apply nth_ext.
  intros p.
  rewrite nth_map; apply H.
Qed.

Lemma compSubstSubst_term { kterm : nat } { lterm : nat } { mterm : nat }
  (sigmaterm : seq (term (kterm)) mterm)
  (tauterm : seq  (term (lterm)) kterm)
  (thetaterm : seq (term (lterm)) mterm)
  (Eqterm : seq_map (subst_term tauterm) sigmaterm = thetaterm)
  (s : term (mterm)) :
    subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s.
Proof.
induction s; cbn.
+ rewrite <- Eqterm, nth_map; reflexivity.
+ f_equal; rewrite seq_map_map; apply nth_ext; intros p.
  rewrite nth_map, H, nth_map; reflexivity.
Qed.

Definition up_subst_subst_term_term { k : nat } { lterm : nat } { mterm : nat }
  (sigma : seq (term (lterm)) k)
  (tauterm : seq  (term (mterm)) lterm)
  (theta : seq (term (mterm)) k)
  (Eq : (seq_map (subst_term tauterm) sigma) = theta) :
  (seq_map (subst_term (up_term_term tauterm)) (up_term_term sigma)) = (up_term_term theta).
Proof.
apply nth_ext; intros [p|].
+ rewrite nth_map; simpl.
  rewrite !nth_map.
  etransitivity; [apply compSubstSubst_term; reflexivity|].
  rewrite <- Eq, !nth_map.
  etransitivity; [|symmetry; apply compSubstSubst_term; reflexivity].
  f_equal; apply nth_ext; clear p; intro p.
  rewrite !nth_map, nth_init.
  unfold funcomp; simpl; rewrite !nth_map; reflexivity.
+ reflexivity.
Qed.

Definition up_subst_subst_list_term_term { p : nat } { k : nat } { lterm : nat } { mterm : nat }
  (sigma : seq (term (lterm)) k)
  (tauterm : seq (term (mterm)) lterm)
  (theta : seq (term (mterm)) k)
  (Eq : (seq_map (subst_term tauterm) sigma) = theta) :
  (seq_map (subst_term (upList_term_term p tauterm)) (upList_term_term p sigma)) = (upList_term_term p theta).
Proof.
apply nth_ext; apply fin_add_rect; intros q.
+ rewrite nth_map.
  unfold upList_term_term.
  rewrite !nth_zero_p, !nth_init; simpl; rewrite nth_zero_p, nth_init; reflexivity.
+ rewrite nth_map.
  unfold upList_term_term.
  rewrite !nth_shift_p, !nth_map; simpl.
  rewrite <- Eq, !nth_map.
  etransitivity; [apply compSubstSubst_term; reflexivity|].
  symmetry; apply compSubstSubst_term.
  rewrite map_init; apply nth_ext; clear q; intro q.
  rewrite !nth_map, !nth_init; cbn.
  rewrite nth_shift_p, nth_map; reflexivity.
Qed.

Lemma varL_term { mterm : nat } { nterm : nat }
  (sigmaterm : seq (term (nterm)) mterm) :
    seq_map (subst_term sigmaterm) (seq_init (var_term (mterm))) = sigmaterm.
Proof.
rewrite map_init; apply nth_ext; intros p; rewrite nth_init; reflexivity.
Qed.

Lemma compComp_term { kterm : nat } { lterm : nat } { mterm : nat }
  (sigmaterm : seq (term (kterm)) mterm)
  (tauterm : seq (term (lterm)) kterm)
  (s : term (mterm)) :
    subst_term tauterm (subst_term sigmaterm s) = subst_term (seq_map (subst_term tauterm) sigmaterm) s.
Proof.
apply compSubstSubst_term; reflexivity.
Qed.

End term.

Section form.

Inductive form (nterm : nat) : Type :=
  | Atm
  : forall (a : atom), seq (term  (nterm)) (atom_arity a) -> form (nterm)
  | Arr : form  (nterm) -> form  (nterm) -> form (nterm)
  | Top : form (nterm)
  | Bot : form (nterm)
  | Cnj : form  (nterm) -> form  (nterm) -> form (nterm)
  | Dsj : form  (nterm) -> form  (nterm) -> form (nterm)
  | All : form  ((S) nterm) -> form (nterm)
  | Exs : form  ((S) nterm) -> form (nterm).

Fixpoint subst_form { mterm : nat } { nterm : nat } (sigmaterm : seq (term (nterm)) mterm) (s : form (mterm)) : form (nterm) :=
    match s with
    | Atm (_) a s0 => Atm (nterm) a ((seq_map (subst_term sigmaterm)) s0)
    | Arr (_) s0 s1 => Arr (nterm) ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | Top (_)  => Top (nterm)
    | Bot (_)  => Bot (nterm)
    | Cnj (_) s0 s1 => Cnj (nterm) ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | Dsj (_) s0 s1 => Dsj (nterm) ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | All (_) s0 => All (nterm) ((subst_form (up_term_term sigmaterm)) s0)
    | Exs (_) s0 => Exs (nterm) ((subst_form (up_term_term sigmaterm)) s0)
    end.

Lemma idSubst_form { mterm : nat }
  (sigmaterm : seq (term (mterm)) mterm)
  (Eqterm : forall x, nth sigmaterm x = (var_term (mterm)) x) (s : form (mterm)) :
    subst_form sigmaterm s = s.
Proof.
induction s; simpl; f_equal; try match goal with [ H : _ |- _] => solve [apply H; assumption] end.
+ apply nth_ext; intros p; rewrite nth_map.
  apply idSubst_term; assumption.
+ apply IHs; apply upId_term_term, Eqterm.
+ apply IHs; apply upId_term_term, Eqterm.
Qed.

Lemma compSubstSubst_form { kterm : nat } { lterm : nat } { mterm : nat }
  (sigmaterm : seq (term (kterm)) mterm)
  (tauterm : seq (term (lterm)) kterm)
  (thetaterm : seq (term (lterm)) mterm)
  (Eqterm : (seq_map (subst_term tauterm) sigmaterm) = thetaterm)
  (s : form (mterm)) :
    subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.
Proof.
revert kterm lterm sigmaterm tauterm thetaterm Eqterm.
induction s; intros kterm lterm sigmaterm tauterm thetaterm Eqterm;
simpl; f_equal; try match goal with [ H : _ |- _] => solve [apply H; assumption] end.
+ rewrite seq_map_map; apply seq_map_ext; intros p.
  apply compSubstSubst_term; assumption.
+ apply IHs.
  apply up_subst_subst_term_term, Eqterm.
+ apply IHs.
  apply up_subst_subst_term_term, Eqterm.
Qed.

End form.

Arguments var_term {nterm}.

Arguments App {nterm}.

Arguments Atm {nterm}.

Arguments Arr {nterm}.

Arguments Top {nterm}.

Arguments Bot {nterm}.

Arguments Cnj {nterm}.

Arguments Dsj {nterm}.

Arguments All {nterm}.

Arguments Exs {nterm}.

Notation "σ >> τ" := (seq_map (subst_term τ) σ) (at level 50, only parsing).
