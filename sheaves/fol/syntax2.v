Axiom symb : Set.
Axiom symb_arity : symb -> nat.
Axiom atom : Set.
Axiom atom_arity : atom -> nat.

Fixpoint fin (n : nat) : Type :=
match n with
| 0 => False
| S m => option (fin m)
end.

Definition fin0 {n : nat} : fin (S n) := None.
Definition finS {n : nat} (p : fin n) : fin (S n) := Some p.

Notation var_zero := fin0.
Notation shift := finS.

Inductive seq (A : Type) : nat -> Type :=
| seq0 : seq A 0
| seqS : forall n, A -> seq A n -> seq A (S n).

Arguments seq0 {_}.
Arguments seqS {_ _}.

Definition seq_map {A B : Type} {n : nat} (f : A -> B) (v : seq A n) : seq B n :=
(fix F n (v : seq A n) :=
match v in seq _ n return seq B n with
| seq0 => seq0
| seqS x v => seqS (f x) (F _ v)
end) n v.

Lemma seq_map_map : forall {A B C} (n : nat) (f : A -> B) (g : B -> C) (v : seq A n),
  seq_map g (seq_map f v) = seq_map (fun x => g (f x)) v.
Proof.
induction v; cbn; [reflexivity|].
f_equal; apply IHv.
Qed.

Lemma seq_map_ext : forall {A B} (n : nat) (f g : A -> B) (v : seq A n),
  (forall x : A, f x = g x) -> seq_map f v = seq_map g v.
Proof.
induction v; intros H; cbn; [reflexivity|].
f_equal; [apply H|]; apply IHv, H.
Qed.

Fixpoint seq_init {A} {n : nat} (f : fin n -> A) : seq A n :=
match n return (fin n -> A) -> seq A n with
| 0 => fun _ => seq0
| S n => fun f => seqS (f var_zero) (@seq_init A n (fun p => f (finS p)))
end f.

Lemma map_init : forall A B n (f : fin n -> A) (g : A -> B),
  seq_map g (seq_init f) = seq_init (fun p => g (f p)).
Proof.
induction n; intros f g; simpl; [reflexivity|].
f_equal; apply IHn.
Qed.

Definition hd {A} {n : nat} (v : seq A (S n)) : A :=
match v in seq _ n return
  match n with 0 => unit | S n => A end
with
| seq0 => tt
| seqS x v => x 
end.

Definition tl {A} {n : nat} (v : seq A (S n)) : seq A n :=
match v in seq _ n return
  match n with 0 => unit | S n => seq A n end
with
| seq0 => tt
| seqS x v => v 
end.

Fixpoint tl_n {A n} (p : nat) : seq A (p + n) -> seq A n :=
match p return seq A (p + n) -> seq A n with
| 0 => fun v => v
| S p => fun v => tl_n p (tl v)
end.

Fixpoint hd_n {A n} (p : nat) : seq A (p + n) -> seq A p :=
match p return seq A (p + n) -> seq A p with
| 0 => fun v => seq0
| S p => fun v =>
  match v in seq _ n return
    match n with 0 => unit | S n => (seq A n -> _) -> seq A (S p) end
  with
  | seq0 => tt
  | seqS x v => fun k => seqS x (k v)
  end (hd_n p)
end.

Fixpoint seq_app {A m n} (v : seq A m) (w : seq A n) : seq A (m + n) :=
match v in seq _ m return seq A n -> seq A (m + n) with
| seq0 => fun w => w
| seqS x v => fun w => seqS x (seq_app v w)
end w.

Lemma seq0_eta : forall A (v : seq A 0), v = seq0.
Proof.
intros A v.
refine (
match v in seq _ n return
  match n return seq A n -> Prop with
  | 0 => fun v => v = seq0
  | S n => fun _ => True
  end v
with
| seq0 => eq_refl
| seqS _ _ => I
end
).
Qed.

Lemma hd_tl : forall A (n : nat) (v : seq A (S n)), v = seqS (hd v) (tl v).
Proof.
intros A n v. 
refine (
match v in seq _ n return
  match n return seq A n -> Prop with
  | 0 => fun _ => True
  | S n => fun (v : seq A (S n)) => v = seqS (hd v) (tl v)
  end v
 with
| seq0 => I
| seqS x v => eq_refl
end
).
Qed.

Lemma hd_tl_n : forall A (p n : nat) (v : seq A (p + n)),
  seq_app (hd_n p v) (tl_n p v) = v.
Proof.
induction p; intros n v; cbn in *; [reflexivity|].
rewrite (hd_tl _ _ v); cbn; rewrite IHp; reflexivity.
Qed.

Fixpoint nth {A n} (v : seq A n) : fin n -> A :=
match v in seq _ n return fin n -> A with
| seq0 =>
  fun p => match p with end
| seqS x v =>
  fun p => match p with
  | None => x
  | Some p => nth v p
  end
end.

Lemma nth_init : forall A (n : nat) (f : fin n -> A) p, nth (seq_init f) p = f p.
Proof.
induction n; cbn.
+ intros f [].
+ intros f [p|]; [|reflexivity].
  apply IHn.
Qed.

Lemma nth_map : forall A B (n : nat) (f : A -> B) (v : seq A n) (p : fin n),
  nth (seq_map f v) p = f (nth v p).
Proof.
induction v; cbn.
+ intros [].
+ intros [p|]; [|reflexivity].
  apply IHv.
Qed.

Lemma nth_ext : forall A n (v w : seq A n),
  (forall p : fin n, nth v p = nth w p) -> v = w.
Proof.
induction n; intros v w e.
+ rewrite (seq0_eta _ v), (seq0_eta _ w); reflexivity.
+ rewrite (hd_tl _ _ v), (hd_tl _ _ w); f_equal.
  - specialize (e None); cbn in e.
    rewrite (hd_tl _ _ v), (hd_tl _ _ w) in e; exact e.
  - apply IHn; intros p.
    specialize (e (Some p)); cbn in e.
    rewrite (hd_tl _ _ v), (hd_tl _ _ w) in e; exact e.
Qed.

Fixpoint zero_p (m : nat) {n : nat} : fin m -> fin (m + n) :=
match m return fin m -> fin (m + n) with
| 0 => fun p => match p with end
| S m => fun p => match p with None => var_zero | Some p => Some (zero_p m p) end
end.

Fixpoint shift_p (m : nat) {n : nat} (p : fin n) : fin (m + n) :=
match m return fin (m + n) with
| 0 => p
| S m => finS (shift_p m p)
end.

Lemma fin_add_rect : forall m n (P : fin (m + n) -> Type),
  (forall p : fin m, P (zero_p _ p)) ->
  (forall p : fin n, P (shift_p _ p)) ->
  forall p : fin (m + n), P p.
Proof.
induction m as [|m IHm]; intros n P Hm Hn p; cbn in *.
+ apply Hn.
+ destruct p as [p|].
  - apply (IHm n (fun p => P (Some p)) (fun p => Hm (Some p)) Hn).
  - apply (Hm None).
Defined.

Lemma nth_zero_p : forall A m n (v : seq A m) (w : seq A n) (p : fin m),
  nth (seq_app v w) (zero_p _ p) = nth v p.
Proof.
induction m; intros n v w p; cbn in *.
+ destruct p.
+ destruct p as [p|]; cbn.
  - rewrite (hd_tl _ _ v); cbn.
    apply IHm.
  - rewrite (hd_tl _ _ v); reflexivity.
Qed.

Lemma nth_shift_p : forall A m n (v : seq A m) (w : seq A n) (p : fin n),
  nth (seq_app v w) (shift_p _ p) = nth w p.
Proof.
induction m; intros n v w p; cbn in *.
+ replace v with (@seq0 A); [reflexivity|].
  symmetry; apply seq0_eta.
+ rewrite (hd_tl _ _ v); cbn.
  apply IHm.
Qed.

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

Notation scons_p := seq_app.

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
