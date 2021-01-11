Set Primitive Projections.

Record site := {
  ste_fun : Prop -> Prop;
  ste_top : forall A : Prop, A -> ste_fun A;
  ste_mon : forall A B : Prop, ste_fun A -> (A -> ste_fun B) -> ste_fun B;
}.

Arguments ste_fun {_}.
Arguments ste_top {_}.
Arguments ste_mon {_}.

Coercion ste_fun : site >-> Funclass.

Record isSheaf (J : site) (A : Type) := {
  shf_elt : forall P : Prop, J P -> (P -> A) -> A;
  shf_spc : forall P (i : J P) (c : P -> A) (x : A),
    (forall p : P, x = c p) -> x = shf_elt P i c;
}.

Arguments shf_elt {_ _}.
Arguments shf_spc {_ _}.

Record isSheaf' (J : site) (A : Type) := {
  shf_elt' : forall P : Prop, J P -> (P -> A) -> A;
  shf_spc' : forall P (i : J P) (x : A), x = shf_elt' P i (fun _ => x);
}.

Axiom funext : forall A (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom pi : forall (A : Prop) (p q : A), p = q.

Lemma sig_eq : forall {A} {P : A -> Prop} (p q : @sig A P), proj1_sig p = proj1_sig q -> p = q.
Proof.
intros A P [p hp] [q hq]; cbn.
revert hq; destruct 1; f_equal; apply pi.
Qed.

Lemma sig_eq_rev : forall {A} {P : A -> Prop} (p q : @sig A P), p = q -> proj1_sig p = proj1_sig q.
Proof.
intros A P p q []; reflexivity.
Qed.


Lemma is_Sheaf_Sheaf' : forall J A, isSheaf' J A -> isSheaf J A.
Proof.
intros J A hA.
unshelve econstructor.
+ refine (fun P i x₀ => hA.(shf_elt' _ _) P i x₀).
+ cbn; intros P i x₀ x hx.
  rewrite (shf_spc' _ _ hA P i x).
  f_equal; apply funext; apply hx.
Defined.

Lemma is_Sheaf'_Sheaf : forall J A, isSheaf J A -> isSheaf' J A.
Proof.
intros J A hA.
unshelve econstructor.
+ refine (fun P i x₀ => hA.(shf_elt) P i x₀).
+ cbn; intros P i x.
  apply shf_spc; constructor.
Defined.

(** Closure under products *)

Lemma Prod_isSheaf : forall (J : site) (A : Type) (B : A -> Type),
  (forall x, isSheaf J (B x)) -> isSheaf J (forall x, B x).
Proof.
intros J A B Bε.
unshelve econstructor.
+ refine (fun P i f x => (Bε x).(shf_elt) P i (fun p => f p x)).
+ intros P i c f hf.
  (** needs funext *)
  apply funext; intros x.
  apply (Bε x).
  intros p; rewrite (hf p); reflexivity.
Defined.

Definition isSeparated (J : site) (A : Type) :=
  forall P (i : J P) (c : P -> A) (x y : A),
      (forall p : P, x = c p) -> (forall p : P, y = c p) -> x = y.

Lemma closed_diag_isSeparated : forall (J : site) A,
  isSeparated J A -> (forall x y : A, J (x = y) -> x = y).
Proof.
intros J A hA x y e.
unshelve refine (hA (x = y) e (fun _ => y) x y (fun e => e) (fun _ => eq_refl)).
Defined.

Lemma isSeparated_closed_diag : forall (J : site) A,
  (forall x y : A, J (x = y) -> x = y) -> isSeparated J A.
Proof.
intros J A hA P i c x y hx hy.
refine (hA _ _ _).
refine (@ste_mon J _ _ i _).
intros p; apply ste_top.
rewrite (hx p), (hy p); reflexivity.
Defined.

Definition PropJ (J : site) := {P : Prop | J P -> P}.

Definition liftJ (J : site) (P : Prop) : PropJ J.
Proof.
exists (J P).
refine (fun p => ste_mon _ _ p (fun p => p)).
Defined.

(** Sheafification à la MacLane-Moerdijk *)

Definition Sh (J : site) (A : Type) :=
  { P : A -> PropJ J | J (exists x : A, forall y, proj1_sig (P y) <-> J (x = y)) }.

Definition Sh_η (J : site) (A : Type) (x : A) : Sh J A.
Proof.
exists (fun y => liftJ J (x = y)).
apply ste_top; exists x; tauto.
Defined.

Definition Sh_bind (J : site) (A B : Type) (m : Sh J A) (f : A -> Sh J B) : Sh J B.
Proof.
destruct m as [P hP].
unshelve econstructor.
+ refine (fun y => liftJ J (exists x : A, proj1_sig (P x) /\ proj1_sig (proj1_sig (f x) y))).
+ refine (ste_mon _ _ hP _); clear hP; intros hP.
  destruct hP as [x hx].
  remember (f x) as Q.
  destruct Q as [Q HQ]; cbn in *.
  refine (ste_mon _ _ HQ _); intros HQ'.
  replace HQ with (@ste_top J _ HQ') in HeqQ by apply pi.
  clear HQ; destruct HQ' as [y hy].
  apply sig_eq_rev in HeqQ; cbn in HeqQ; subst Q.
  apply ste_top; exists y; intros y'; split; intro H.
  - refine (ste_mon _ _ H _); clear H; intros [x' [Hl Hr]].
    assert (e : J (x = x')).
    { apply hx; assumption. }
    refine (ste_mon _ _ e _); clear e; intros e; subst x'.
    apply hy; assumption.
  - refine (ste_mon _ _ H _); clear H; intros H; subst y'.
    apply ste_top; exists x; split.
    { apply hx, ste_top; reflexivity. }
    { apply hy, ste_top; reflexivity. }
Defined.

Lemma isSheaf_subobj (J : site) (A : Type) (P : A -> Prop)
  (hA : isSheaf J A) (hP : forall x, J (P x) -> P x) : isSheaf J {x : A | P x}.
Proof.
apply is_Sheaf_Sheaf'.
apply is_Sheaf'_Sheaf in hA.
unshelve econstructor.
+ intros Q j x.
  unshelve econstructor.
  - refine (hA.(shf_elt' _ _) Q j (fun q => proj1_sig (x q))).
  - apply hP.
    unshelve refine (@ste_mon J _ _ j _).
    intro j'; apply ste_top.
    replace (fun q => proj1_sig (x q)) with (fun _ : Q => proj1_sig (x j')).
    2: { apply funext; intros j''; repeat f_equal; apply pi. }
    rewrite <- (shf_spc' J A hA Q j).
    destruct (x j'); cbn; assumption.
+ intros Q j [x hx]; cbn.
  match goal with [ |- _ = exist ?P ?x ?p ] => generalize p as hx' end.
  rewrite <- shf_spc'; intros; f_equal; apply pi.
Defined.

Axiom propext : forall (A B : Prop), (A <-> B) -> A = B.

Lemma isSeparated_Sh : forall J A, isSeparated J (Sh J A).
Proof.
intros J A; apply isSeparated_closed_diag. intros [P HP] [Q HQ] H; cbn.
apply sig_eq; cbn.
apply funext; intros z. apply sig_eq; apply propext.
match goal with [ |- ?P ] => cut (J P) end.
+ clear; intros H; split; intros H';
  match goal with [ |- proj1_sig ?P ] => apply (proj2_sig P) end;
  refine (ste_mon _ _ H _); intros []; apply ste_top; tauto.
+ refine (ste_mon _ _ H _); clear H; intros H.
  apply sig_eq_rev in H; cbn in H.
  rewrite H; apply ste_top; tauto.
Defined.

Lemma PropJ_isSheaf (J : site) : isSheaf J (PropJ J).
Proof.
apply is_Sheaf_Sheaf'; unshelve econstructor.
+ intros P i f.
  unshelve econstructor.
  { refine (forall p : P, proj1_sig (f p)). }
  { intros j p.
    remember (f p) as Q; destruct Q as [Q HQ]; cbn in *.
    apply HQ.
    refine (ste_mon _ _ j _).
    intros g.
    specialize (g p).
    rewrite <- HeqQ in g; cbn in g.
    apply ste_top; assumption.
  }
+ intros P i [Q HQ]; cbn.
  apply sig_eq; cbn.
  apply propext; split; [tauto|].
  intros f. apply HQ.
  refine (ste_mon _ _ i _).
  intros p; apply ste_top; tauto.
Defined.

Lemma isSheaf_Sh : forall J A, isSeparated J A -> isSheaf J (Sh J A).
Proof.
intros J A HA.
apply isSheaf_subobj.
+ apply Prod_isSheaf; intros; apply PropJ_isSheaf.
+ intros P HP.
  refine (ste_mon _ _ HP (fun x => x)).
Defined.

Lemma Sh_bind_η : forall J A (x : Sh J A), Sh_bind J A _ x (Sh_η J A) = x.
Proof.
intros J A [P HP].
apply sig_eq; cbn.
apply funext; intros x; cbn.
apply sig_eq; cbn; apply propext.
split; intros H.
+ apply (proj2_sig (P x)).
  refine (ste_mon _ _ H _); clear H; intros [y [Hy e]].
  refine (ste_mon _ _ e _); clear e; intros ->; apply ste_top; assumption.
+ apply ste_top; exists x; split.
  - assumption.
  - apply ste_top; reflexivity.
Qed.

Lemma Sh_η_bind : forall J A B (x : A) f, Sh_bind J A B (Sh_η J A x) f = f x.
Proof.
intros J A B x f; apply sig_eq; cbn.
apply funext; intros y; cbn; apply sig_eq; cbn; apply propext; split; intros H.
+ apply (proj2_sig (proj1_sig (f x) y)).
  refine (ste_mon _ _ H _); clear H; intros [x' [e Hx]].
  refine (ste_mon _ _ e _); clear e; intros e; subst x'.
  apply ste_top; assumption.
+ apply ste_top; exists x; split.
  - apply ste_top; reflexivity.
  - assumption.
Qed.

Lemma Sh_bind_bind : forall J A B C (x : Sh J A) f g,
  Sh_bind J B C (Sh_bind J A B x f) g = Sh_bind J A C x (fun x => Sh_bind J B C (f x) g).
Proof.
intros J A B C [P HP] f g; apply sig_eq; cbn.
apply funext; intros z; apply sig_eq; cbn; apply propext; cbn; split; intros H.
+ refine (ste_mon _ _ H _); clear H; intros [y [hy hg]].
  refine (ste_mon _ _ hy _); clear hy; intros [x [hx hf]].
  apply ste_top; exists x; split; [assumption|].
  remember (f x) as Q; destruct Q as [Q HQ]; cbn.
  apply sig_eq_rev in HeqQ; cbn in HeqQ; subst Q; cbn in *.
  apply ste_top; exists y; split; [assumption|].
  assumption.
+ refine (ste_mon _ _ H _); clear H; intros [x [hx hf]].
  remember (f x) as Q; destruct Q as [Q HQ]; cbn.
  apply sig_eq_rev in HeqQ; cbn in HeqQ; subst Q; cbn in *.
  refine (ste_mon _ _ hf _); clear hf; intros [y [hy hz]].
  apply ste_top; exists y; split; [|assumption].
  apply ste_top; exists x; split; assumption.
Qed.

Lemma Sh_idempotent : forall J A (x : Sh J A),
  Sh_η J (Sh J A) x = Sh_bind J A (Sh J A) x (fun x => Sh_η J (Sh J A) (Sh_η J A x)).
Proof.
intros J A [P HP]; cbn; apply sig_eq; cbn.
apply funext; intros [Q HQ]; apply sig_eq; cbn.
apply propext; cbn; split; intros H.
+ refine (ste_mon _ _ H _); clear H; intros H.
  apply sig_eq_rev in H; cbn in H.
  subst Q; replace HQ with HP by apply pi; clear HQ.
  refine (ste_mon _ _ HP _); intros HP'.
  replace HP with (@ste_top J _ HP') by apply pi; clear HP; rename HP' into HP.
  destruct HP as [x Hx]; apply ste_top; exists x.
  split; [now apply Hx, ste_top, eq_refl|].
  apply ste_top; apply sig_eq; cbn.
  apply funext; intros x'; apply sig_eq, propext; cbn; split;
  intros; apply Hx; assumption.
+ cut (J (P = Q)).
  { clear H; intros H.
    refine (ste_mon _ _ H _); clear H; intros H.
    revert HP HQ; destruct H; intros HP HQ.
    replace HP with HQ by apply pi; apply ste_top; reflexivity. }
  refine (ste_mon _ _ H _); clear H; intros [x [Hx H]].
  refine (ste_mon _ _ H _); clear H; intros H; apply sig_eq_rev in H; cbn in H.
  rewrite <- H; clear Q HQ H.
  refine (ste_mon _ _ HP _); clear HP; intros [x' HP].
  assert (e : J (x' = x)).
  { apply HP; assumption. }
  refine (ste_mon _ _ e _); clear e; intro e; subst x'.
  apply ste_top; apply funext; intros x'; apply sig_eq; apply propext; split; intros H; cbn in *.
  - apply HP; assumption.
  - apply HP; assumption.
Qed.

Axiom choice : forall A (P : A -> Prop), (exists x, P x) -> {x : A | P x}.

Definition Sh_alg {J A} (hA : isSheaf J A) (x : Sh J A) : A.
Proof.
destruct x as [P HP].
unshelve refine (hA.(shf_elt) _ HP _).
refine (fun H => proj1_sig (choice _ _ H)).
Defined.

(* Lemma Sh_alg_η : forall J A (hA : isSeparated J A) (x : A),
  Sh_alg (isSheaf_Sh J A hA) (Sh_η J A x) = x. *)

(** Sheafification with quotients *)

Axiom Quo : forall (A : Type) (R : A -> A -> Prop), Type.
Axiom quo : forall {A} R (x : A), Quo A R.
Axiom quo_eq : forall {A} {R : A -> A -> Prop} (x y : A) (e : R x y), quo R x = quo R y.

Axiom quo_rect : forall {A} {R : A -> A -> Prop} (P : Quo A R -> Type)
    (u : forall x : A, P (quo R x))
    (uε : forall (x y : A) (r : R x y), match quo_eq x y r in _ = z return P z with eq_refl => u x end = u y),
    forall q : Quo A R, P q.

Axiom quo_rect_eq : forall A R P u uε (x : A), @quo_rect A R P u uε (quo R x) = u x.

Definition quo_elim : forall {A} {R : A -> A -> Prop} (P : Type)
    (u : A -> P)
    (uε : forall (x y : A) (r : R x y), u x = u y),
    forall q : Quo A R, P.
Proof.
refine (fun A R P u uε => @quo_rect A R (fun _ => P) u _).
{ intros x y r; destruct (@quo_eq A R x y r); apply uε, r. }
Defined.

Lemma quo_elim_eq : forall A R P u uε (x : A), @quo_elim A R P u uε (quo R x) = u x.
Proof.
intros; unfold quo_elim.
refine (quo_rect_eq _ _ _ _ _ _).
Qed.

Inductive clos {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| clos_incl : forall x y, R x y -> clos R x y
| clos_refl : forall x, clos R x x
| clos_trns : forall x y z, clos R x y -> clos R y z -> clos R x z
| clos_symm : forall x y, clos R x y -> clos R y x.

(** We need propext to prove this from the other quotient axioms??? *)
Axiom quo_inv : forall {A} {R : A -> A -> Prop} (x y : A) (e : quo R x = quo R y), clos R x y.


Record T (J : site) (A : Type) := {
  t_prp : Prop;
  t_prf : J t_prp;
  t_elt : (t_prp -> A);
}.

Arguments t_prp {_ _}.
Arguments t_prf {_ _}.
Arguments t_elt {_ _}.

Definition Tr {J A} (x y : T J A) : Prop :=
  exists (α : x.(t_prp) -> y.(t_prp)), forall (p : x.(t_prp)), x.(t_elt) p = y.(t_elt) (α p).

Definition ShQ J A := Quo (T J A) Tr.

(*
Lemma Tr_eq : forall (J : site) (A : Type) (pX pY : T J A)
  (p : t_prp pX) (q : t_prp pY), clos Tr pY pX -> t_elt pX p = t_elt pY q.
Proof.
induction 1.
+ destruct H as [α e].
  symmetry; replace p with (α q) by apply pi.
  apply e.
+ replace p with q by apply pi; reflexivity.
+ transitivity.
  - apply IHclos2.
  - apply IHclos1.
+ symmetry; apply IHclos.
Qed.
*)

Lemma Tr_eq : forall (J : site) (A : Type) (P : Prop) (i : J P) 
  (x : P -> A) (Q : Prop) (j : J Q) (y : Q -> A),
  quo Tr {| t_prp := Q; t_prf := j; t_elt := y |} =
  quo Tr {| t_prp := P; t_prf := i; t_elt := x |} ->
  forall (p : P) (q : Q), x p = y q.
Proof.
Admitted.

Lemma isSeparated_Q : forall J (A : Type), isSeparated J (ShQ J A).
Proof.
intros J A R k c x y hx hy.
revert x hx y hy; unshelve refine (quo_rect _ (fun x hx => quo_rect _ (fun y hy => _) _) _).
+ destruct x as [P i x].
  destruct y as [Q j y].
  unshelve refine (let z : T J A := Build_T J A (R /\ P /\ Q) _ _ in _).
  { refine (ste_mon _ _ i (fun i => ste_mon _ _ j (fun j => ste_mon _ _ k (fun k => ste_top _ (conj k (conj i j)))))). }
  { intros [_ [p _]]; refine (x p). }
  transitivity (quo Tr z); [symmetry|]; apply quo_eq.
  - unshelve econstructor; cbn.
    { intros [_ [p _]]; exact p. }
    { intros [_ [p _]]; reflexivity. }
  - unshelve econstructor; cbn.
    { intros [_ [_ q]]; exact q. }
    { intros [r [p q]].
      clear z.
      specialize (hx r).
      specialize (hy r).
      rewrite <- hx in hy; clear hx.
      eapply Tr_eq, hy.
    }
+ intros; apply pi.
+ intros; apply pi.
Defined.

Lemma isSheaf_ShQ : forall J (A : Type), isSeparated J A -> isSheaf J (ShQ J A).
Proof.
intros J A hA.

unshelve econstructor.
+ intros P i x.
  refine (quo _ _); unshelve econstructor.
  - refine (exists p : P, _).
(*
    unshelve refine (quo_elim Prop _ _ (x p)).
    { intros [Q _ _]; exact (P /\ Q). }
    { clear - hA; intros [Q j y] [R k z].
      intros [α f]; cbn in *.
cbn.
*)
  exact True.
  - admit.
  - intros r.
    unshelve refine (quo_elim _ _ _ (x _)).
    
intros [p q].


Definition bind {J A B} : Q J A -> (A -> Q J B) -> Q J B.
Proof.
intros x f.
revert x.
unshelve refine (Q_rect _ _ _).
+ intros P i φ.
  apply f.
  apply φ.

Lemma isSheaf_Q : forall J (A : Type), isSheaf J (Q J (Q J A)).
Proof.
intros J A.
unshelve econstructor.
+ intros P i φ.
  unshelve refine (qc P i (fun p => _)).
  specialize (φ p).
  revert φ.
  clear.
  unshelve refine (Q_rect _ _ _).
  - intros R j ψ.
    unshelve refine (qc R j _).
    
Abort.
