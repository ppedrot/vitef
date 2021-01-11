Require Export fintype. Require Export header_extensible.

Axiom symb : Set.
Axiom symb_arity : symb -> nat.
Axiom atom : Set.
Axiom atom_arity : atom -> nat.

Section term.
Inductive term (nterm : nat) : Type :=
  | var_term : (fin) (nterm) -> term (nterm)
  | App
  : forall (s : symb), cod (fin (symb_arity s)) (term  (nterm)) -> term (nterm).

Lemma congr_App { s : symb } { mterm : nat } { s0 : cod (fin (symb_arity s)) (term  (mterm)) } { t0 : cod (fin (symb_arity s)) (term  (mterm)) } (H1 : s0 = t0) : App (mterm) s s0 = App (mterm) s t0 .
Proof. congruence. Qed.

Fixpoint subst_term { mterm : nat } { nterm : nat } (sigmaterm : (fin) (mterm) -> term (nterm)) (s : term (mterm)) : term (nterm) :=
    match s with
    | var_term (_) s => sigmaterm s
    | App (_) s s0 => App (nterm) s ((cod_map (subst_term sigmaterm)) s0)
    end.

Definition up_term_term { m : nat } { nterm : nat } (sigma : (fin) (m) -> term (nterm)) : (fin) ((S) (m)) -> term ((S) nterm) :=
  (scons) ((var_term ((S) nterm)) (var_zero)) ((funcomp) (subst_term ((funcomp) (var_term (_)) (shift))) sigma).

Definition upList_term_term (p : nat) { m : nat } { nterm : nat } (sigma : (fin) (m) -> term (nterm)) : (fin) (p+ (m)) -> term (p+ nterm) :=
  scons_p  p ((funcomp) (var_term (p+ nterm)) (zero_p p)) ((funcomp) (subst_term ((funcomp) (var_term (_)) (shift_p p))) sigma).

Definition upId_term_term { mterm : nat } (sigma : (fin) (mterm) -> term (mterm)) (Eq : forall x, sigma x = (var_term (mterm)) x) : forall x, (up_term_term sigma) x = (var_term ((S) mterm)) x :=
  fun n => match n with
  | Some fin_n => (ap) (subst_term ((funcomp) (var_term (_)) (shift))) (Eq fin_n)
  | None => eq_refl
  end.

Definition upIdList_term_term { p : nat } { mterm : nat } (sigma : (fin) (mterm) -> term (mterm)) (Eq : forall x, sigma x = (var_term (mterm)) x) : forall x, (upList_term_term p sigma) x = (var_term (p+ mterm)) x :=
  fun n => scons_p_eta (var_term (p+ mterm)) (fun n => (ap) (subst_term ((funcomp) (var_term (_)) (shift_p p))) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_term { mterm : nat } (sigmaterm : (fin) (mterm) -> term (mterm)) (Eqterm : forall x, sigmaterm x = (var_term (mterm)) x) (s : term (mterm)) : subst_term sigmaterm s = s :=
    match s with
    | var_term (_) s => Eqterm s
    | App (_) s s0 => congr_App ((cod_id (idSubst_term sigmaterm Eqterm)) s0)
    end.

Definition upExt_term_term { m : nat } { nterm : nat } (sigma : (fin) (m) -> term (nterm)) (tau : (fin) (m) -> term (nterm)) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (subst_term ((funcomp) (var_term (_)) (shift))) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_list_term_term { p : nat } { m : nat } { nterm : nat } (sigma : (fin) (m) -> term (nterm)) (tau : (fin) (m) -> term (nterm)) (Eq : forall x, sigma x = tau x) : forall x, (upList_term_term p sigma) x = (upList_term_term p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (subst_term ((funcomp) (var_term (_)) (shift_p p))) (Eq n)).

Fixpoint ext_term { mterm : nat } { nterm : nat } (sigmaterm : (fin) (mterm) -> term (nterm)) (tauterm : (fin) (mterm) -> term (nterm)) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term (mterm)) : subst_term sigmaterm s = subst_term tauterm s :=
    match s with
    | var_term (_) s => Eqterm s
    | App (_) s s0 => congr_App ((cod_ext (ext_term sigmaterm tauterm Eqterm)) s0)
    end.

Fixpoint compSubstSubst_term { kterm : nat } { lterm : nat } { mterm : nat } (sigmaterm : (fin) (mterm) -> term (kterm)) (tauterm : (fin) (kterm) -> term (lterm)) (thetaterm : (fin) (mterm) -> term (lterm)) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : term (mterm)) : subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s with
    | var_term (_) s => Eqterm s
    | App (_) s s0 => congr_App ((cod_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s0)
    end.

Definition up_subst_subst_term_term { k : nat } { lterm : nat } { mterm : nat } (sigma : (fin) (k) -> term (lterm)) (tauterm : (fin) (lterm) -> term (mterm)) (theta : (fin) (k) -> term (mterm)) (Eq : forall x, ((funcomp) (subst_term tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compSubstSubst_term ((funcomp) (var_term (_)) (shift)) (up_term_term tauterm) ((funcomp) (up_term_term tauterm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_term tauterm ((funcomp) (var_term (_)) (shift)) ((funcomp) (subst_term ((funcomp) (var_term (_)) (shift))) tauterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_term ((funcomp) (var_term (_)) (shift))) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_list_term_term { p : nat } { k : nat } { lterm : nat } { mterm : nat } (sigma : (fin) (k) -> term (lterm)) (tauterm : (fin) (lterm) -> term (mterm)) (theta : (fin) (k) -> term (mterm)) (Eq : forall x, ((funcomp) (subst_term tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (upList_term_term p tauterm)) (upList_term_term p sigma)) x = (upList_term_term p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_term (p+ lterm)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => subst_term ((funcomp) (var_term (_)) (shift_p p)) (_)) x) (fun n => (eq_trans) (compSubstSubst_term ((funcomp) (var_term (_)) (shift_p p)) (upList_term_term p tauterm) ((funcomp) (upList_term_term p tauterm) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_term tauterm ((funcomp) (var_term (_)) (shift_p p)) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (subst_term ((funcomp) (var_term (_)) (shift_p p))) (Eq n))))).

Lemma instId_term { mterm : nat } : subst_term (var_term (mterm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_term (mterm)) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_term { mterm : nat } { nterm : nat } (sigmaterm : (fin) (mterm) -> term (nterm)) : (funcomp) (subst_term sigmaterm) (var_term (mterm)) = sigmaterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term { kterm : nat } { lterm : nat } { mterm : nat } (sigmaterm : (fin) (mterm) -> term (kterm)) (tauterm : (fin) (kterm) -> term (lterm)) (s : term (mterm)) : subst_term tauterm (subst_term sigmaterm s) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term { kterm : nat } { lterm : nat } { mterm : nat } (sigmaterm : (fin) (mterm) -> term (kterm)) (tauterm : (fin) (kterm) -> term (lterm)) : (funcomp) (subst_term tauterm) (subst_term sigmaterm) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaterm tauterm n)). Qed.

End term.

Section form.
Inductive form (nterm : nat) : Type :=
  | Atm
  : forall (a : atom), cod (fin (atom_arity a)) (term  (nterm)) -> form (nterm)
  | Arr : form  (nterm) -> form  (nterm) -> form (nterm)
  | Top : form (nterm)
  | Bot : form (nterm)
  | Cnj : form  (nterm) -> form  (nterm) -> form (nterm)
  | Dsj : form  (nterm) -> form  (nterm) -> form (nterm)
  | All : form  ((S) nterm) -> form (nterm)
  | Exs : form  ((S) nterm) -> form (nterm).

Lemma congr_Atm { a : atom } { mterm : nat } { s0 : cod (fin (atom_arity a)) (term  (mterm)) } { t0 : cod (fin (atom_arity a)) (term  (mterm)) } (H1 : s0 = t0) : Atm (mterm) a s0 = Atm (mterm) a t0 .
Proof. congruence. Qed.

Lemma congr_Arr { mterm : nat } { s0 : form  (mterm) } { s1 : form  (mterm) } { t0 : form  (mterm) } { t1 : form  (mterm) } (H1 : s0 = t0) (H2 : s1 = t1) : Arr (mterm) s0 s1 = Arr (mterm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Top { mterm : nat } : Top (mterm) = Top (mterm) .
Proof. congruence. Qed.

Lemma congr_Bot { mterm : nat } : Bot (mterm) = Bot (mterm) .
Proof. congruence. Qed.

Lemma congr_Cnj { mterm : nat } { s0 : form  (mterm) } { s1 : form  (mterm) } { t0 : form  (mterm) } { t1 : form  (mterm) } (H1 : s0 = t0) (H2 : s1 = t1) : Cnj (mterm) s0 s1 = Cnj (mterm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Dsj { mterm : nat } { s0 : form  (mterm) } { s1 : form  (mterm) } { t0 : form  (mterm) } { t1 : form  (mterm) } (H1 : s0 = t0) (H2 : s1 = t1) : Dsj (mterm) s0 s1 = Dsj (mterm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_All { mterm : nat } { s0 : form  ((S) mterm) } { t0 : form  ((S) mterm) } (H1 : s0 = t0) : All (mterm) s0 = All (mterm) t0 .
Proof. congruence. Qed.

Lemma congr_Exs { mterm : nat } { s0 : form  ((S) mterm) } { t0 : form  ((S) mterm) } (H1 : s0 = t0) : Exs (mterm) s0 = Exs (mterm) t0 .
Proof. congruence. Qed.

Fixpoint subst_form { mterm : nat } { nterm : nat } (sigmaterm : (fin) (mterm) -> term (nterm)) (s : form (mterm)) : form (nterm) :=
    match s with
    | Atm (_) a s0 => Atm (nterm) a ((cod_map (subst_term sigmaterm)) s0)
    | Arr (_) s0 s1 => Arr (nterm) ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | Top (_)  => Top (nterm)
    | Bot (_)  => Bot (nterm)
    | Cnj (_) s0 s1 => Cnj (nterm) ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | Dsj (_) s0 s1 => Dsj (nterm) ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | All (_) s0 => All (nterm) ((subst_form (up_term_term sigmaterm)) s0)
    | Exs (_) s0 => Exs (nterm) ((subst_form (up_term_term sigmaterm)) s0)
    end.

Fixpoint idSubst_form { mterm : nat } (sigmaterm : (fin) (mterm) -> term (mterm)) (Eqterm : forall x, sigmaterm x = (var_term (mterm)) x) (s : form (mterm)) : subst_form sigmaterm s = s :=
    match s with
    | Atm (_) a s0 => congr_Atm ((cod_id (idSubst_term sigmaterm Eqterm)) s0)
    | Arr (_) s0 s1 => congr_Arr ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    | Top (_)  => congr_Top 
    | Bot (_)  => congr_Bot 
    | Cnj (_) s0 s1 => congr_Cnj ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    | Dsj (_) s0 s1 => congr_Dsj ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    | All (_) s0 => congr_All ((idSubst_form (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    | Exs (_) s0 => congr_Exs ((idSubst_form (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    end.

Fixpoint ext_form { mterm : nat } { nterm : nat } (sigmaterm : (fin) (mterm) -> term (nterm)) (tauterm : (fin) (mterm) -> term (nterm)) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form (mterm)) : subst_form sigmaterm s = subst_form tauterm s :=
    match s with
    | Atm (_) a s0 => congr_Atm ((cod_ext (ext_term sigmaterm tauterm Eqterm)) s0)
    | Arr (_) s0 s1 => congr_Arr ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    | Top (_)  => congr_Top 
    | Bot (_)  => congr_Bot 
    | Cnj (_) s0 s1 => congr_Cnj ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    | Dsj (_) s0 s1 => congr_Dsj ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    | All (_) s0 => congr_All ((ext_form (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    | Exs (_) s0 => congr_Exs ((ext_form (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    end.

Fixpoint compSubstSubst_form { kterm : nat } { lterm : nat } { mterm : nat } (sigmaterm : (fin) (mterm) -> term (kterm)) (tauterm : (fin) (kterm) -> term (lterm)) (thetaterm : (fin) (mterm) -> term (lterm)) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form (mterm)) : subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s :=
    match s with
    | Atm (_) a s0 => congr_Atm ((cod_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s0)
    | Arr (_) s0 s1 => congr_Arr ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1)
    | Top (_)  => congr_Top 
    | Bot (_)  => congr_Bot 
    | Cnj (_) s0 s1 => congr_Cnj ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1)
    | Dsj (_) s0 s1 => congr_Dsj ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1)
    | All (_) s0 => congr_All ((compSubstSubst_form (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0)
    | Exs (_) s0 => congr_Exs ((compSubstSubst_form (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0)
    end.

Lemma instId_form { mterm : nat } : subst_form (var_term (mterm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form (var_term (mterm)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form { kterm : nat } { lterm : nat } { mterm : nat } (sigmaterm : (fin) (mterm) -> term (kterm)) (tauterm : (fin) (kterm) -> term (lterm)) (s : form (mterm)) : subst_form tauterm (subst_form sigmaterm s) = subst_form ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form { kterm : nat } { lterm : nat } { mterm : nat } (sigmaterm : (fin) (mterm) -> term (kterm)) (tauterm : (fin) (kterm) -> term (lterm)) : (funcomp) (subst_form tauterm) (subst_form sigmaterm) = subst_form ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form sigmaterm tauterm n)). Qed.

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

Global Instance Subst_term { mterm : nat } { nterm : nat } : Subst1 ((fin) (mterm) -> term (nterm)) (term (mterm)) (term (nterm)) := @subst_term (mterm) (nterm) .

Global Instance Subst_form { mterm : nat } { nterm : nat } : Subst1 ((fin) (mterm) -> term (nterm)) (form (mterm)) (form (nterm)) := @subst_form (mterm) (nterm) .

Global Instance VarInstance_term { mterm : nat } : Var ((fin) (mterm)) (term (mterm)) := @var_term (mterm) .

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope.

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_term X Y := up_term : X -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Global Instance Up_term_term { m : nat } { nterm : nat } : Up_term (_) (_) := @up_term_term (m) (nterm) .

Notation "s [ sigmaterm ]" := (subst_term sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_term sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form sigmaterm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_form,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_form,  VarInstance_term in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?instId_form| progress rewrite ?compComp_form| progress rewrite ?compComp'_form| progress rewrite ?varL_term| progress (unfold up_ren, up_term_term, upList_term_term)| progress (cbn [subst_term subst_form])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?instId_form in *| progress rewrite ?compComp_form in *| progress rewrite ?compComp'_form in *| progress rewrite ?varL_term in *| progress (unfold up_ren, up_term_term, upList_term_term in *)| progress (cbn [subst_term subst_form] in *)| fsimpl in *].

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.
