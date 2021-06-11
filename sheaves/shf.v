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

Axiom funext : forall A (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom pi : forall (A : Prop) (p q : A), p = q.

Ltac unwrap :=
repeat match goal with
| [ H : @ste_fun ?J ?P |- ste_fun _ ] =>
  let H' := fresh H in
  refine (ste_mon _ _ H (fun H' => _));
  replace H with (@ste_top J _ H') in * by apply pi;
  clear H; rename H' into H
end.

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

Lemma isSheaf_hProp : forall J A (p q : isSheaf J A), p = q.
Proof.
intros J A [f hf] [g hg].
assert (e : f = g).
+ apply funext; intros P; apply funext; intros i; apply funext; intros x.
  apply hg; intros p.
  symmetry; apply hf; intros p'.
  f_equal; apply pi.
+ revert hf hg; rewrite e; intros.
  replace hf with hg by apply pi; reflexivity.
Qed.

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
unwrap.
apply ste_top.
rewrite (hx i), (hy i); reflexivity.
Defined.

Lemma isSeparated_isSheaf : forall (J : site) A,
  isSheaf J A -> isSeparated J A.
Proof.
intros J A hA P i c x y hx hy.
rewrite (shf_spc hA P i c); [|apply hy].
rewrite <- (shf_spc hA P i c x); [|apply hx].
reflexivity.
Qed.

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
+ unwrap.
  destruct hP as [x hx].
  remember (f x) as Q.
  destruct Q as [Q HQ]; cbn in *.
  unwrap.
  destruct HQ as [y hy].
  apply sig_eq_rev in HeqQ; cbn in HeqQ; subst Q.
  apply ste_top; exists y; intros y'; split; intro H.
  - refine (ste_mon _ _ H _); clear H; intros [x' [Hl Hr]].
    assert (e : J (x = x')).
    { apply hx; assumption. }
    unwrap; subst x'.
    apply hy; assumption.
  - unwrap; subst y'.
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

Lemma Sh_alg_η : forall J A (hA : isSheaf J A) (x : A),
  Sh_alg hA (Sh_η J A x) = x.
Proof.
intros J A hA x.
unfold Sh_alg; cbn.
symmetry; apply shf_spc; intros [y Hy].
destruct choice as [z Hz]; cbn.
apply closed_diag_isSeparated with J.
+ apply isSeparated_isSheaf, hA.
+ specialize (Hy x); specialize (Hz x).
  assert (i : J (y = x)).
  { apply Hy, ste_top; reflexivity. }
  assert (j : J (z = x)).
  { apply Hz, ste_top; reflexivity. }
  refine (ste_mon _ _ i (fun i => ste_mon _ _ j _)).
  intros []; apply ste_top; reflexivity.
Qed.

(** Sheafification with quotients *)
Module QuotientSh.

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

Record T (J : site) (A : Type) := {
  t_prp : Prop;
  t_prf : J t_prp;
  t_elt : (t_prp -> A);
}.

Arguments t_prp {_ _}.
Arguments t_prf {_ _}.
Arguments t_elt {_ _}.

Record Tr₀ {J A} (x y : T J A) (P : Prop) : Prop := {
  tr_prf : J P;
  tr_hom : P -> x.(t_prp) /\ y.(t_prp);
  tr_eqv : forall (p : P), x.(t_elt) (proj1 (tr_hom p)) = y.(t_elt) (proj2 (tr_hom p));
}.

Definition Tr {J A} x y := exists P, (@Tr₀ J A x y P).

Lemma Tr_refl : forall J A x, @Tr J A x x.
Proof.
intros J A x.
exists (t_prp x); unshelve econstructor.
+ tauto.
+ destruct x; tauto.
+ intros p; cbn; f_equal; apply pi.
Qed.

Lemma Tr_sym : forall J A x y, @Tr J A x y -> Tr y x.
Proof.
intros J A x y [P [i f v]].
exists P; unshelve econstructor.
+ intros; split; apply f; assumption.
+ assumption.
+ intros p; symmetry.
  specialize (v p).
  etransitivity; [|etransitivity]; [|apply v|]; f_equal; apply pi.
Qed.

Lemma Tr_trans : forall J A x y z, @Tr J A x y -> Tr y z -> Tr x z.
Proof.
intros J A x y z [P [i f v]] [Q [j g w]].
exists (P /\ Q); unshelve econstructor.
+ intros [? ?]; split; [apply f|apply g]; assumption.
+ unwrap; apply ste_top; tauto.
+ intros [p q].
  match goal with [ |- _ _ ?p = _ _ ?q ] => set (l := p); set (r := q); clearbody l r end.
  replace l with (proj1 (f p)) by apply pi.
  etransitivity; [apply v|].
  replace r with (proj2 (g q)) by apply pi.
  replace (proj2 (f p)) with (proj1 (g q)) by apply pi.
  apply w.
Qed.

Definition ShQ J A := Quo (T J A) Tr.

Lemma ShQ_eq : forall J A p q, quo Tr p = quo Tr q -> @Tr J A p q.
Proof.
intros J A p q e.
simple refine (let T := quo_rect (fun x => Prop) (fun x => Tr x q) _ (quo Tr p) in _).
{ intros x y r.
  destruct quo_eq; apply propext; split; intros;
  eapply Tr_trans; first [eassumption|apply Tr_sym; eassumption|idtac]. }
replace (Tr p q) with T; unfold T.
2:{ rewrite quo_rect_eq; reflexivity. }
rewrite e, quo_rect_eq.
apply Tr_refl.
Qed.

Definition ofSh {J A} (x : Sh J A) : ShQ J A.
Proof.
unfold ShQ.
destruct x as [Px Hx].
apply quo.
refine (Build_T _ _ _ Hx _).
intros H; apply choice in H.
destruct H as [x hx].
exact x.
Defined.

Lemma ste_iff_map : forall (J : site) A B, (A <-> B) -> (J A <-> J B).
Proof.
intros J A B [Hl Hr]; split; intros H; refine (ste_mon _ _ H _); intro; apply ste_top; intuition.
Qed.

Lemma toSh_subproof (J : site) (P : Prop) A (k : P -> A) (i : J P) :
  J (exists x : A, forall y : A, J (forall p : P, y = k p) <-> J (x = y)).
Proof.
refine (ste_mon _ _ i (fun p => _)).
apply ste_top; exists (k p); intros y.
apply ste_iff_map; split; intros H.
+ symmetry; apply H.
+ intros p'; replace p' with p by apply pi; symmetry; assumption.
Qed.

Definition toSh {J A} (x : ShQ J A) : Sh J A.
Proof.
revert x.
unshelve refine (quo_rect _ _ _).
+ intros [P i k].
  pose (join P (x : J (J P)) := @ste_mon J _ _ x (fun x => x)).
  unshelve refine (exist _ (fun x => exist _ (J (forall p, x = k p)) (join _)) _).
  apply toSh_subproof, i.
+ intros x y r; cbn.
  apply sig_eq; cbn.
  apply funext; intros z; cbn.
  apply sig_eq; cbn.
  set (e := quo_eq x y r); clearbody e.
  destruct e; cbn.
  destruct r as [P [i f e]]; cbn in *.
  destruct x as [X ix kx], y as [Y iy ky]; cbn in *.
  apply propext; split; intros H.
  - refine (ste_mon _ _ i (fun i => ste_mon _ _ H (fun H => ste_top _ _))).
    intros p; rewrite (H (proj1 (f i))), e; f_equal; apply pi.
  - refine (ste_mon _ _ i (fun i => ste_mon _ _ H (fun H => ste_top _ _))).
    intros p; rewrite (H (proj2 (f i))), <- e; f_equal; apply pi.
Defined.

Lemma toSh_ofSh : forall J A (x : Sh J A), toSh (ofSh x) = x.
Proof.
intros J A [P HP]; cbn.
apply sig_eq; cbn.
apply funext; intros x; apply sig_eq; cbn.
unfold toSh; cbn.
rewrite quo_rect_eq; cbn.
apply propext; split; intros H.
+ apply (proj2_sig (P x)).
  refine (ste_mon _ _ HP (fun HP => ste_mon _ _ H (fun H => _))).
  clear H0 HP0.
  specialize (H HP); cbn in *.
  destruct choice as [y Hy].
  subst y.
  apply ste_top, Hy, ste_top, eq_refl.
+ refine (ste_mon _ _ HP (fun HP => _)); clear HP0.
  destruct HP as [y Hy].
  assert (e : J (y = x)).
  { apply Hy; assumption. }
  refine (ste_mon _ _ e (fun e => _)); clear e0.
  subst y.
  assert (e : exists z, forall y, proj1_sig (P y) <-> J (z = y)).
  { exists x; assumption. }
  match goal with [ |- _ ?P ] => replace P with (x = proj1_sig (choice _ _ e)) end.
  2:{ apply propext; split; intros.
      + replace p with e by apply pi; assumption.
      + apply H0. }
  destruct choice as [w Hw]; cbn.
  cut (J (w = x)); [|apply Hw; assumption].
  intros Hr.
  refine (ste_mon _ _ Hr (fun Hr => ste_top _ _)); congruence.
Qed.

Lemma ofSh_toSh : forall J A (x : ShQ J A), ofSh (toSh x) = x.
Proof.
intros J A.
unshelve refine (quo_rect _ _ _).
+ intros [P i k]; cbn.
  unfold toSh; rewrite quo_rect_eq; cbn.
  apply quo_eq; cbn.
  exists ((exists x : A, forall y : A, (forall p : P, y = k p <-> x = y)) /\ P);  unshelve econstructor.
  - cbn; intros [_ p]; split; [|assumption].
    { exists (k p); intros y.
      apply ste_iff_map; split; [now intuition|].
      intros [] q; f_equal; apply pi. }
  - unwrap; apply ste_top; split; [|assumption].
    exists (k i); intros y q.
    replace q with i by apply pi; split; congruence.
  - cbn; intros [e p].
    destruct choice as [x Hx]; cbn.
    match goal with [ |- x = k ?p ] => set (q := p); clearbody q end.
        
    specialize (Hx (k p)).
    admit.
+ intros x y r.
  apply pi.
Abort.

Lemma isSeparated_ShQ : forall J (A : Type), isSeparated J (ShQ J A).
Proof.
intros J A R k c x y hx hy.
cut (forall p : R, x = y).
2:{ intros r; rewrite (hx r), <- (hy r); reflexivity. }
clear c hx hy.
revert x y.
unshelve refine (quo_rect _ (fun x => quo_rect _ (fun y => _) _) _).
+ intros e.
  apply quo_eq.
  destruct x as [P i x], y as [Q j y].
  (** Needs functional choice *)
  assert (eR := fun r => choice _ _ (ShQ_eq _ _ _ _ (e r))); clear e; rename eR into e.
  exists (P /\ Q /\ exists r : R, proj1_sig (e r)).
  unshelve econstructor.
  - cbn; intros [p [q r]]; split; assumption.
  - unwrap.
    set (S r := proj1_sig (e r)).
    assert (l : J (S k)); [|clearbody S; clear e].
    { clear - e; unfold S; destruct e as [? [? ? ?]]; assumption. }
    unwrap.
    apply ste_top; now intuition eauto.
  - intros [p [q [r s]]]; cbn.
    destruct e as [S [l h z]]; cbn in *; clear e.
    specialize (z s).
    etransitivity; [|etransitivity]; [|apply z|]; f_equal; apply pi.
+ intros; apply pi.
+ intros; apply pi.
Qed.

Lemma isSheaf_ShQ : forall J (A : Type), isSeparated J A -> isSheaf J (ShQ J A).
Proof.
intros J A hA.
(* assert (hShA := isSeparated_ShQ J A). *)
unshelve econstructor.
+ intros P i x.
  simple refine (let R : P -> Prop := fun p => _ in _).
  { simple refine (@quo_rect _ _ (fun _ => Prop) (fun p => J (t_prp p)) _ (x p)); cbn.
    abstract (intros [Q j y] [R k z] e; destruct quo_eq; apply propext; cbn in *; tauto). }
  apply quo.
  exists (exists p : P, R p).
  - unwrap.
    assert (j : R i).
    { unfold R. generalize (x i); clear - hA.
      simple refine (quo_rect _ _ _); cbn.
      + intros [Q j y].
        rewrite quo_rect_eq; cbn; assumption.
      + intros; apply pi. }
    apply ste_top; exists i; assumption.
  - intros H.
    assert (i' : P) by (destruct H; assumption).
    clear i; rename i' into i.
    assert (j : R i).
    { destruct H as [i' j]; replace i with i' by apply pi; assumption. }
    clear H.
    unfold R in j; clear R.
    set (H := isSheaf_ShQ_subproof J A P x i) in j; clearbody H.
    set (x' := x i) in *; clearbody x'; clear x; rename x' into x.
    revert x H j.
    simple refine (quo_rect _ _ _); cbn.
    * intros [Q j y] H; cbn.
      rewrite quo_rect_eq; cbn.
    
Abort.

Definition ShQ_η {J A} (x : A) : ShQ J A :=
  quo _ (Build_T _ _ True (ste_top _ I) (fun _ => x)).

(*
Lemma ShQ_univ {J A B} (hB : isSheaf J B) (f : A -> B) (x : ShQ J A) : B.
Proof.
revert x.
simple refine (quo_rect _ _ _); cbn.
+ intros [P i x].
  refine (hB.(shf_elt) P i (fun p => f (x p))).
+ intros [P i x] [Q j y] [T [k h z]]; simpl in *.
  apply hB.(shf_spc); intros q.
  match goal with [ |- (match ?p with eq_refl => _ end = _) ] => set (e := p); clearbody e end.
*)

Definition ShQ_bind {J A B} (x : ShQ J A) (f : A -> ShQ J B) : ShQ J B.
Proof.
revert x.
simple refine (quo_rect _ _ _); cbn.
+ intros [P i x].
  refine (quo _ _).
  simple refine (let R : P -> Prop := fun p => _ in _).
  { simple refine (@quo_rect _ _ (fun _ => Prop) t_prp _ (f (x p))); cbn.
    intros y z r.
    destruct quo_eq.
  (* Global choice *)
Abort.

Definition ShQ_alg {J A} (hA : isSheaf J A) (x : ShQ J A) : A.
Proof.
destruct hA as [hA eA].
revert x; simple refine (quo_rect _ _ _).
+ intros [P i x].
  apply (hA P i x).
+ intros x y e; cbn.
  apply eA; intros q.
  destruct quo_eq.
  symmetry; apply eA; intros p.
  destruct e as [R [k ? e]].
  transitivity (hA R k (fun _ => t_elt x p)).
  - apply eA; intros r.
    symmetry; etransitivity; [|etransitivity]; [|apply (e r)|]; f_equal; apply pi.
  - symmetry; apply eA; intros r; reflexivity.
Defined.

Lemma ShQ_alg_η : forall J A (hA : isSheaf J A) (x : A),
  ShQ_alg hA (ShQ_η x) = x.
Proof.
intros J A hA x.
unfold ShQ_alg, ShQ_η.
rewrite quo_rect_eq.
symmetry; apply shf_spc; intros; reflexivity.
Qed.


End QuotientSh.

Module DialogueSh.

Axiom ShD : site -> Type -> Type.
Axiom ret : forall {J A}, A -> ShD J A.
Axiom ask : forall {J : site} {A} (P : Prop) (i : J P), (P -> ShD J A) -> ShD J A.
Axiom eqn : forall (J : site) A P (i : J P) (x : ShD J A),
  ask P i (fun (_ : P) => x) = x.

Axiom ShD_rect : forall (J : site) (A : Type) (P : ShD J A -> Type)
  (ur : forall (x : A), P (ret x))
  (ua : forall (S : Prop) (i : J S) (k : S -> ShD J A),
    (forall p : S, P (k p)) -> P (ask S i k))
  (ue : forall (S : Prop) (i : J S) (x : ShD J A) (px : P x),
    match eqn J A S i x in _ = e return P e with eq_refl => ua S i (fun _ => x) (fun _ => px) end = px)
  (x : ShD J A)
,
  P x.
(* P (ask S i (fun _ => x) *)

Axiom ShD_rect_ret : forall J A P ur ua ue (x : A),
  ShD_rect J A P ur ua ue (ret x) = ur x. 

Axiom ShD_rect_ask : forall (J : site) A P ur ua ue (S : Prop) (i : J S) (k : S -> ShD J A),
  ShD_rect J A P ur ua ue (ask S i k) = ua S i k (fun p => ShD_rect J A P ur ua ue (k p)). 

Definition bind {J A B} (m : ShD J A) (f : A -> ShD J B) : ShD J B.
Proof.
simple refine (ShD_rect _ _ (fun _ => ShD J B) f (fun S i k r => ask S i r) _ m).
{
  cbn; intros S i x y.
  destruct eqn; apply eqn.
}
Defined.

Lemma ret_bind : forall J A B (x : A) (f : A -> ShD J B), bind (ret x) f = f x.
Proof.
intros; unfold bind; cbn.
rewrite ShD_rect_ret; reflexivity.
Qed.

Lemma bind_ret : forall J A (m : ShD J A) , bind m ret = m.
Proof.
intros; unfold bind; cbn; revert m.
simple refine (ShD_rect _ _ _ _ _ _); cbn.
+ intros x.
  rewrite ShD_rect_ret; reflexivity.
+ intros S i k e; rewrite ShD_rect_ask.
  f_equal; apply funext; intros s.
  rewrite (e s); reflexivity.
+ intros; apply pi.
Qed.

Lemma bind_assoc : forall J A B C (f : A -> ShD J B) (g : B -> ShD J C) (m : ShD J A),
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
intros J A B C f g.
simple refine (ShD_rect _ _ _ _ _ _); unfold bind; cbn.
+ intros x.
  rewrite !ShD_rect_ret; cbn; reflexivity.
+ intros S i k e.
  rewrite !ShD_rect_ask; f_equal; apply funext; intros s.
  rewrite (e s).
  reflexivity.
+ intros; apply pi.
Qed.

(*

Γ ⊢ P : bool → Type
Γ ⊢ ut : P true
Γ ⊢ uf : P false
================
_ : Π b : bool, P b

Γ, b : bool ⊢ P is a type
Γ ⊢ ut : P true
Γ ⊢ uf : P false
================
_ : Π b : bool, P b


*)

(* Small elimination *)
Lemma bool_dep_elim : forall J
  (P : ShD J bool -> Type) (Pε : forall b, isSheaf J (P b))
  (ut : P (ret true))
  (uf : P (ret false))
  (b : ShD J bool),
  P b.
Proof.
intros J P Pε ut uf.
simple refine (ShD_rect _ _ _ _ _ _); [intros [|]| |].
+ apply ut.
+ apply uf.
+ refine (fun S i k r => _).
  refine ((Pε (ask S i k)).(shf_elt) S i (fun s => _)).
  replace k with (fun (_ : S) => k s).
  2: { abstract (apply funext; intros; f_equal; apply pi). }
  rewrite eqn.
  apply r.
+ intros S i x r; cbn in *.
  set (e := eqn J bool S i x); clearbody e.
  match goal with [ |- context [ shf_elt _ _ _ ?f ] ] => set (k := f) end; cbn in k.
  pose (r' := match e in _ = x' return P x' -> P (ask S i (fun _ => x)) with eq_refl => fun r => r end r).
  replace (shf_elt (Pε (ask S i (fun _ : S => x))) S i k) with r'; unfold r'; clear r'.
  2:{ apply shf_spc; intros s; unfold k.
      unfold eq_rect_r, eq_rect, eq_sym.
      set (rw := bool_dep_elim_subproof J S (fun _ : S => x) s); clearbody rw.
      assert (e' : rw = eq_refl) by apply pi.
      cbn in rw; rewrite e'.
      rewrite e; reflexivity.
      }
  clear.
  rewrite e; reflexivity.
Qed.



(** The result of sheafifying is a sheaf... *)
Lemma isSheaf_ShD J A : isSheaf J (ShD J A).
Proof.
  apply is_Sheaf_Sheaf'.
  exists ask.
  intros; symmetry ; apply eqn.
Defined.

Lemma shf_elt_ShD J A S i h : shf_elt (isSheaf_ShD J A) S i h = ask S i h.
Proof. reflexivity. Defined.


(* mu and map combinators on ShD *)

Definition mu {J A} (m : ShD J (ShD J A)) := bind m (fun x => x).

Definition map {J A B} (f : A -> B) (m : ShD J A) : ShD J B := bind m (fun x => ret (f x)).

Lemma map_ret {J A B} (f : A -> B) (x : A) : map (J:=J) f (ret x) = ret (f x).
Proof. unfold map; now rewrite ret_bind. Qed.

(* Probably the most surpising lemma of the bunch
   Equivalent to the idempotence of ShD according to nlab *)
Lemma map_ret' {J A} : forall (x : ShD J A), map ret x = ret x.
Proof.
  simple refine (ShD_rect _ _ _ _ _ _); cbn.
  - intros; now rewrite map_ret.
  - intros. unfold map, bind. rewrite ShD_rect_ask.
    set (h := fun _ => _); set (x := ret _).
    assert (h = fun _ => x) as ->; [| apply eqn].
    apply funext; intro p.
    specialize H with p.
    unfold h, x. clear h x.
    unfold map, bind in H.
    rewrite H.
    f_equal.
    symmetry.
    assert (k = fun _ => k p) as ->; [|apply eqn].
    apply funext. intros. f_equal; apply pi.
  - intros; apply pi.
Qed.

Definition map_cmp {J A B C} (f : A -> B) (g : B -> C) (m : ShD J A) :
  map g (map f m) = map (fun x=> g (f x)) m.
Proof.
  unfold map.
  rewrite bind_assoc.
  f_equal. apply funext; intros ?. rewrite ret_bind. reflexivity.
Qed.


(** Algebra structure on ShD  and lemmas *)

Definition ShD_alg {J A} (hA : isSheaf J A) : ShD J A -> A.
Proof.
  simple refine (ShD_rect _ _ _ _ _ _); [trivial| ..].
  - intros S i k h; cbn; apply (shf_elt hA S i h).
  - cbn; intros S i x px. destruct (eqn J A S i x).
    symmetry; apply shf_spc; reflexivity.
Defined.

(* ShD_alg is a two sided inverse to ret *)
Lemma ShD_alg_ret {J A} (hA : isSheaf J A) : forall x,  ShD_alg hA (ret x) = x.
Proof. intros; unfold ShD_alg; now rewrite ShD_rect_ret. Qed.

Lemma ret_ShD_alg {J A} (hA : isSheaf J A) : forall x,  ret (ShD_alg hA  x) = x.
Proof.
  intros x.
  rewrite <- map_ret.
  rewrite <- map_ret'.
  rewrite map_cmp.
  set (h := fun _ => _); assert (h = fun x => x) as ->.
  + apply funext; intros; unfold h; now rewrite ShD_alg_ret.
  + unfold map; now rewrite bind_ret.
Qed.

(* The algebra structure on a free sheave is.. free *)
Lemma ShD_alg_free {J A} : forall (m : ShD J (ShD J A)),
  ShD_alg (isSheaf_ShD J A) m = mu m.
Proof.
  simple refine (ShD_rect _ _ _ _ _ _); cbn.
  - intros. unfold mu.
    now rewrite ShD_alg_ret, ret_bind.
  - intros S i k h.
    unfold ShD_alg, mu, bind; rewrite !ShD_rect_ask, shf_elt_ShD.
    f_equal; apply funext; intro p.
    apply (h p).
  - cbn; intros. apply pi.
Qed.


(** Every map between types is an algebra homomorphism *)
Lemma ShD_homomorphism {J A B} (hA : isSheaf J A) (hB : isSheaf J B) (f : A -> B) (m : ShD J A) :
  ShD_alg hB (map f m) = f (ShD_alg hA m).
Proof.
  now rewrite <- (ret_ShD_alg hA m), map_ret, ShD_alg_ret, (ret_ShD_alg hA m).
Qed.


(** Being a sheaf is closed under dependent sum *)

(* technical lemma on eq_rect *)
Lemma rew_swap' :
  forall (A : Type) (P : A -> Type) (x1 x2 : A) (H : x1 = x2)
    (y1 : P x1) (y2 : P x2),
  eq_rect_r P y2 H = y1 -> y2 = eq_rect x1 P y1 x2 H.
Proof.
  intros ? ? ? ? h ? ? e.
  rewrite <- (rew_opp_r _ h y2).
  rewrite e.
  reflexivity.
Qed.

Lemma sigma_sheaf : forall J A (Aε : isSheaf J A)
  (B : A -> Type) (Bε : forall a, isSheaf J (B a)),
    isSheaf J { a : A & B a}.
Proof.
  intros.
  unshelve econstructor.
  - intros P i f. exists (shf_elt Aε P i (fun p => projT1 (f p))).
    apply (shf_elt (Bε _) P i).
    intro x.
    rewrite <- shf_spc with (x0:= projT1 (f x)).
    exact (projT2 (f x)).
    intro; do 2 f_equal; apply pi.
  - intros; destruct x as [x1 x2].
    simple refine (eq_existT_curried _ _ ).
    + apply shf_spc. intro p; exact (f_equal (projT1 (P:=B)) (H p)).
    + apply shf_spc; intro p.
      set (e1 := shf_spc _ _ _ _ _ _).
      set (e2 := shf_spc _ _ _ _ _ _).
      apply rew_swap'; unfold eq_rect_r; rewrite rew_compose.
      rewrite <- (projT2_eq (H p)).
      f_equal. apply pi.
Defined.


Section Complicated_bool_dep_elim.
  (**
     Another way to derive the small dependent eliminator on Bool
     using the closure of sheaves under Sigma types
     (trying to understand what is necessary to obtain this kind of elimination)

     It does not look like a good challenger for its computational content,
     even though in the (strict) setoid model it probably just works®
     (that is simpl_b (ret b) ≡ eq_refl)
   *)
  Context J
          (P : ShD J bool -> Type) (Pε : forall b, isSheaf J (P b))
          (ut : P (ret true))
          (uf : P (ret false)).

  Definition P' b := P (ret b).
  Definition Pε' b : isSheaf J (P' b) := Pε (ret b).
  Definition pack_with_pf b :=
    existT P (ret b) (if b as b0 return (P' b0) then ut else uf).

  Definition alg := ShD_alg (sigma_sheaf J (ShD J bool) (isSheaf_ShD J bool) P Pε).

  Lemma simpl_b (b : ShD J bool) : projT1 (alg (map pack_with_pf b)) = b.
  Proof.
    unfold alg; rewrite <- (ShD_homomorphism _ (isSheaf_ShD J bool)), map_cmp.
    cbn; now rewrite map_ret', ShD_alg_ret.
  Qed.

  Definition bool_dep_elim'  (b : ShD J bool) : P b :=
    eq_rect _ P (projT2 (alg (map pack_with_pf b))) b (simpl_b b).
End Complicated_bool_dep_elim.




