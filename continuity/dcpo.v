Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Program Cases.

Inductive Box@{i} (A : Type@{i}) : SProp := box : A -> Box A.
Inductive Inj@{i} (A : SProp) : Type@{i} := inj : A -> Inj A.
Inductive False : SProp :=.
Inductive True : SProp := I.

Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
(* Axiom propext : forall (A B : SProp), (A -> B) -> (B -> A) -> A = B. *)
Axiom pirrel : forall (A : Prop) (x y : A), x = y.
Axiom classical : forall (A : Type), A + (A -> Logic.False).

Definition unbox  {A : Prop} (x : Box A) : A.
Proof.
destruct (classical A); [assumption|].
enough False as [].
destruct x as [x]; elim (f x).
Qed.

Set Primitive Projections.

Record sig (A : Type) (B : A -> Type) := pair {
  fst : A;
  snd : B fst;
}.

Arguments pair {_ _}.
Arguments fst {_ _}.
Arguments snd {_ _}.

Definition prod (A B : Type) := sig A (fun _ => B).

Record subset (A : Type) (B : A -> SProp) := ex {
  wit : A;
  spc : B wit;
}.

Arguments ex {_ _}.
Arguments wit {_ _}.
Arguments spc {_ _}.

Inductive exist (A : Type) (P : A -> SProp) : SProp := thereis : forall x : A, P x -> exist A P.

Arguments thereis {_ _}.

Record and (A B : SProp) : SProp := conj { proj1 : A; proj2 : B }.

Definition iff (A B : SProp) := and (A -> B) (B -> A).

Lemma iff_reflexivity : forall A, iff A A.
Proof.
intros ?; split; auto.
Qed.

Lemma iff_transitivity : forall A B C, iff A B -> iff B C -> iff A C.
Proof.
intros ??? [] []; split; auto.
Qed.

Lemma choice : forall {A : Type}, Box A -> A.
Proof.
intros.
destruct (classical A) as [x|k]; [assumption|].
exfalso; apply unbox; elim H; intros; constructor; auto.
Qed.

Lemma absurdum : forall A : SProp, ((A -> False) -> False) -> A.
Proof.
intros A.
destruct (classical (subset unit (fun _ => A))) as [[]|k]; auto.
intros k'; elim k'; intros x; elim k; now exists tt.
Qed.

(** End of prelude *)

Record lub {A} (R : A -> A -> SProp) (D : A -> SProp) (u : A) : SProp := {
  lub_ub : forall x, D x -> R x u;
  lub_lb : forall v, (forall x, D x -> R x v) -> R u v;
}.

Record is_ub {A} (R : A -> A -> SProp) (D : A -> SProp) (x y : A) (u : A) : SProp := {
  ub_spc : D u;
  ub_lft : R x u;
  ub_rgt : R y u;
}.

Definition directed {A} (R : A -> A -> SProp) (D : A -> SProp) :=
  forall (x y : A), D x -> D y -> exist A (fun z => is_ub R D x y z).

Definition monotonous {A B : Type} (RA : A -> A -> SProp) (RB : B -> B -> SProp) (f : A -> B) := forall x y : A,
  RA x y -> RB (f x) (f y).

Inductive maprel {A B} (D : A -> SProp) (f : A -> B) (y : B) : SProp :=
| maprel_intro0 : forall x, y = f x -> D x -> maprel D f y.

Lemma maprel_intro {A B} D (f : A -> B) x : D x -> maprel D f (f x).
Proof.
intros d; exists x; auto.
Qed.

Lemma directed_maprel : forall {A B : Type} {RA RB} {D : A -> SProp} {f : A -> B},
  monotonous RA RB f ->
  directed RA D -> directed RB (maprel D f).
Proof.
intros A B RA RB D f Hf d; intros y1 y2 H1 H2.
destruct H1 as [x1 ? H1]; subst.
destruct H2 as [x2 ? H2]; subst.
specialize (d x1 x2 H1 H2) as [z [Hz Hxz Hyz]].
exists (f z); split.
+ now exists z.
+ apply Hf, Hxz.
+ apply Hf, Hyz.
Qed.

Record is_dcpo (A : Type) (R : A -> A -> SProp) (sup : forall D, directed R D -> A) : SProp := {
  dcpo_refl : forall x, R x x;
  dcpo_trns : forall x y z, R x y -> R y z -> R x z;
  dcpo_irfl : forall x y, R x y -> R y x -> Box (x = y);
  dcpo_ssup : forall D (d : directed R D), lub R D (sup D d);
}.

Record dcpo := {
  dcpo_car : Type;
  dcpo_rel : dcpo_car -> dcpo_car -> SProp;
  dcpo_sup : forall D, directed dcpo_rel D -> dcpo_car;
  dcpo_spc : is_dcpo dcpo_car dcpo_rel dcpo_sup;
}.

Coercion dcpo_car : dcpo >-> Sortclass.

Notation "⊔ D" := (dcpo_sup _ D _) (at level 10).

Lemma dcpo_refl_intro : forall (A : dcpo) (x y : A), dcpo_rel A x y -> dcpo_rel A y x -> x = y.
Proof.
intros.
eapply choice, dcpo_irfl; eauto using dcpo_spc.
Qed.

Lemma dcpo_refl_elim : forall (A : dcpo) (x y : A), x = y -> dcpo_rel A x y.
Proof.
intros; subst; eapply dcpo_refl, A.
Qed.

Lemma dcpo_sup_intro : forall (A : dcpo) D d (x : A),
  D x -> dcpo_rel A x (dcpo_sup A D d).
Proof.
intros * Hx; assert (H := dcpo_ssup _ _ _ A.(dcpo_spc) D); now apply H.
Qed.

Lemma dcpo_sup_elim : forall (A : dcpo) D d (x : A),
  (forall x' : A, D x' -> dcpo_rel A x' x) -> dcpo_rel A (dcpo_sup A D d) x.
Proof.
intros *; assert (H := dcpo_ssup _ _ _ A.(dcpo_spc) D); apply H.
Qed.

Lemma dcpo_transitivity : forall (A : dcpo) (x y z : A),
  dcpo_rel A x y -> dcpo_rel A y z -> dcpo_rel A x z.
Proof.
intros; eapply dcpo_trns; try eassumption; apply A.
Qed.

Lemma directed_empty : forall A RA D, (forall x, D x -> False) -> @directed A RA D.
Proof.
intros * H x y Hx Hy; elim (H x Hx).
Qed.

Definition dcpo_bot (A : dcpo) := dcpo_sup A (fun _ => False) (directed_empty _ _ _ (fun _ => False_sind _)).

Lemma dcpo_bot_spec : forall (A : dcpo) (x : A), dcpo_rel A (dcpo_bot A) x.
Proof.
intros; apply dcpo_sup_elim; intros ? [].
Qed.

Inductive flat_rel {A} : option A -> option A -> SProp :=
| flat_rel_None : flat_rel None None
| flat_rel_Some : forall x, flat_rel (Some x) (Some x)
| flat_rel_None_Some : forall x, flat_rel None (Some x).

Definition flat_sup {A : Type} (D : option A -> SProp) (d : directed flat_rel D) : option A :=
match classical (sig A (fun x => Inj (D (Some x)))) with
| inl x => Some (fst x)
| inr _ => None
end.

Program Definition Flat (A : Type) : dcpo := Build_dcpo (option A) flat_rel flat_sup _.
Next Obligation.
intros; split.
+ intros [x|]; constructor.
+ intros [x|] [y|] [z|]; inversion 1; subst; inversion 1; subst; constructor.
+ intros [x|] [y|]; inversion 1; subst; inversion 1; subst; repeat constructor.
+ intros D d; split.
  - intros x Hx; unfold flat_sup.
    destruct classical as [[y [Hy]]|]; cbn.
    * destruct x as [x|]; [|constructor].
      specialize (d _ _ Hx Hy) as [z [Hz Hxz Hyz]].
      inversion Hxz; subst; inversion Hyz; subst; constructor.
    * destruct x as [x|]; [|constructor].
      elim f; now exists x.
  - intros v Hv; unfold flat_sup.
    destruct classical as [[y [Hy]]|]; cbn.
    * now apply Hv.
    * destruct v; constructor.
Qed.

Definition ℕ := Flat nat.

Lemma monotonous_sup_le : forall {A B : dcpo} D d (f : A -> B)
  (m : monotonous (dcpo_rel A) (dcpo_rel B) f),
  B.(dcpo_rel) (B.(dcpo_sup) (maprel D f) (directed_maprel m d)) (f (A.(dcpo_sup) D d)).
Proof.
intros.
apply dcpo_sup_elim.
intros y [x ? Hx]; subst; apply m.
now apply dcpo_sup_intro.
Qed.

Record continuous {A B : dcpo} (f : A -> B) : SProp := {
  cont_mono : monotonous (dcpo_rel A) (dcpo_rel B) f;
  cont_sup : forall D (d : directed (dcpo_rel A) D),
    exist A D ->
    B.(dcpo_rel) (f (A.(dcpo_sup) D d)) (B.(dcpo_sup) (maprel D f) (directed_maprel cont_mono d));
}.

Arguments cont_mono {_ _ _}.
Arguments cont_sup {_ _ _}.

Record arr_car (A B : dcpo) := {
  arr_fun : A -> B;
  arr_spc : continuous arr_fun;
}.

Arguments arr_spc {_ _}.

Coercion arr_fun : arr_car >-> Funclass.

Lemma continuous_sup : forall {A B : dcpo} D d (f : arr_car A B),
  exist A D ->
  (f (A.(dcpo_sup) D d)) = (B.(dcpo_sup) (maprel D f) (directed_maprel f.(arr_spc).(cont_mono) d)).
Proof.
intros.
eapply unbox, dcpo_irfl; [apply dcpo_spc| |].
+ now apply cont_sup.
+ apply monotonous_sup_le.
Qed.

Lemma maprel_bind_l : forall {A B C} P (f : A -> B) (g : B -> C) (z : C),
  iff (maprel (maprel P f) g z) (maprel P (fun x => g (f x)) z).
Proof.
intros; split.
+ intros [y ? Hy]; subst.
  destruct Hy as [x ? Hx]; subst.
  now exists x.
+ intros [x ? ?]; subst.
  exists (f x); [reflexivity|].
  exists x; auto using Inj.
Qed.

Lemma dcpo_arr_monotonous : forall {A B : dcpo} (f : arr_car A B), monotonous (dcpo_rel A) (dcpo_rel B) f.
Proof.
intros; apply cont_mono, arr_spc.
Qed.

Definition arr_rel {A B : dcpo} (f g : arr_car A B) := forall x : A, dcpo_rel B (f x) (g x).

Lemma arr_rel_app : forall {A B : dcpo} (f g : arr_car A B) (x y : A),
  arr_rel f g -> dcpo_rel A x y -> dcpo_rel B (f x) (g y).
Proof.
intros * Hfg Hxy; apply dcpo_transitivity with (f y).
+ now apply f.
+ apply Hfg.
Qed.

Definition aprel {A B} (D : arr_car A B -> SProp) (x : A) : B -> SProp := maprel D (fun f => f x).

Lemma aprel_intro {A B D} (f : arr_car A B) (x : A) : D f -> aprel D x (f x).
Proof.
intros; exists f; auto.
Qed.

Lemma directed_aprel : forall {A B : dcpo} D (x : A) ,
  directed arr_rel D -> directed (dcpo_rel B) (aprel D x).
Proof.
intros; eapply directed_maprel; [|now eauto].
intros f g Hfg; apply Hfg.
Qed.

Lemma arr_sup_monotonous : forall {A B : dcpo} (D : arr_car A B -> SProp) (d : directed arr_rel D),
  monotonous (dcpo_rel A) (dcpo_rel B) (fun x => dcpo_sup B (aprel D x) (directed_aprel _ _ d)).
Proof.
intros * x1 x2 Hx.
apply dcpo_sup_elim.
intros ? [f ? ?]; subst.
eapply dcpo_transitivity with (y := f x2).
+ now apply arr_spc.
+ apply dcpo_sup_intro.
  exists f; [reflexivity|auto].
Qed.

Lemma dcpo_sup_monotonous : forall (A : dcpo) D1 D2
  (d1 : directed (dcpo_rel A) D1) (d2 : directed (dcpo_rel A) D2),
  (forall x, D1 x -> D2 x) -> dcpo_rel A (dcpo_sup A D1 d1) (dcpo_sup A D2 d2).
Proof.
intros * H.
apply dcpo_sup_elim; intros x Hx.
now apply dcpo_sup_intro, H.
Qed.

Lemma directed_ext : forall A R (D1 D2 : A -> SProp),
  directed R D1 -> (forall x, iff (D1 x) (D2 x)) -> directed R D2.
Proof.
intros A R D1 D2 H1 H x y Hx Hy.
specialize (H1 x y); destruct H1 as [u []]; try now apply H.
exists u; split; auto.
now apply H.
Qed.

Lemma dcpo_sup_ext : forall (A : dcpo) D1 D2
  (d1 : directed (dcpo_rel A) D1) (d2 : directed (dcpo_rel A) D2),
  (forall x, iff (D1 x) (D2 x)) -> dcpo_sup A D1 d1 = dcpo_sup A D2 d2.
Proof.
intros * H.
apply unbox; eapply dcpo_irfl; [apply A|..].
+ apply dcpo_sup_monotonous; intros; now apply H.
+ apply dcpo_sup_monotonous; intros; now apply H.
Qed.

Lemma dcpo_sup_ext' : forall (A : dcpo) D1 D2
  (d1 : directed (dcpo_rel A) D1)
  (H : forall x, iff (D1 x) (D2 x)), dcpo_sup A D1 d1 = dcpo_sup A D2 (directed_ext _ _ _ _ d1 H).
Proof.
intros; now apply dcpo_sup_ext.
Qed.

Lemma continuous_comp : forall {A B C : dcpo} (f : A -> B) (g : B -> C),
  continuous f -> continuous g -> continuous (fun x => g (f x)).
Proof.
intros * Hf Hg; unshelve econstructor.
+ intros x x' Hx; apply Hg, Hf, Hx.
+ intros D d xd.
  pose (f0 := Build_arr_car _ _ f Hf).
  pose (g0 := Build_arr_car _ _ g Hg).
  change f with (arr_fun _ _ f0).
  rewrite (continuous_sup D d f0); [|assumption].
  change g with (arr_fun _ _ g0).
  assert (yd : exist B (maprel D f0)).
  { destruct xd as [x xd]; exists (f0 x); now apply maprel_intro. }
  rewrite (continuous_sup _ _ g0); [|assumption].
  apply dcpo_sup_monotonous; intros z; apply maprel_bind_l.
Qed.

Program Definition arr_sup {A B : dcpo} (D : arr_car A B -> SProp) (d : directed arr_rel D) :=
  Build_arr_car A B (fun x => dcpo_sup B (aprel D x) (directed_aprel _ _ d)) _.
Next Obligation.
intros; unshelve eexists.
+ apply arr_sup_monotonous.
+ intros DA dx xd.
  apply dcpo_sup_elim; intros y [f ? Hf]; subst.
  rewrite continuous_sup.
  apply dcpo_sup_elim; intros ? [x ? Hx]; subst.
  assert (dap := directed_aprel D x d).
  eapply dcpo_transitivity with (y := dcpo_sup B _ dap).
  - now apply dcpo_sup_intro, aprel_intro.
  - clear f Hf.
    eapply dcpo_sup_intro.
    exists x; now repeat constructor.
  - assumption.
Qed.

Program Definition Arr (A B : dcpo) : dcpo := Build_dcpo (arr_car A B) arr_rel arr_sup _.
Next Obligation.
intros A B; split.
+ intros f x; eapply dcpo_refl, dcpo_spc.
+ intros f g h Hl Hr x.
  now eapply dcpo_transitivity.
+ intros [f] [g] Hl Hr; constructor.
  assert (e : f = g); [|destruct e; reflexivity].
  apply funext; intros x; apply unbox.
  eapply dcpo_irfl; [apply B|apply Hl|apply Hr].
+ intros D d; split.
  - intros f Hf x; unfold arr_sup.
    set (dx := directed_aprel D x d).
    pose proof (dcpo_ssup _ _ _ B.(dcpo_spc) _ dx).
    now apply H, aprel_intro.
  - intros f Hf x; unfold arr_sup.
    set (dx := directed_aprel D x d).
    pose proof (dcpo_ssup _ _ _ B.(dcpo_spc) _ dx).
    apply H; intros y Hy.
    destruct Hy as [h ? ?]; subst.
    now apply Hf.
Qed.

Notation "A → B" := (Arr A B) (at level 99, right associativity, B at level 200).

Program Definition Comp {A B C} (f : A → B) (g : B → C) : A → C := {| arr_fun := fun x => g (f x) |}.
Next Obligation.
intros; apply continuous_comp; [apply f|apply g].
Qed.

Record prd_rel {A B : dcpo} (p q : prod A B) : SProp := {
  prdrel_fst : dcpo_rel A (fst p) (fst q);
  prdrel_snd : dcpo_rel B (snd p) (snd q);
}.

Lemma directed_fst : forall {A B : dcpo} (D : prod A B -> SProp),
  directed (@prd_rel A B) D -> directed (dcpo_rel A) (maprel D fst).
Proof.
intros; eapply directed_maprel; [|now eauto].
intros [x y] [x' y'] []; cbn in *; eauto.
Qed.

Lemma directed_snd : forall {A B : dcpo} (D : prod A B -> SProp),
  directed (@prd_rel A B) D -> directed (dcpo_rel B) (maprel D snd).
Proof.
intros; eapply directed_maprel; [|now eauto].
intros [x y] [x' y'] []; cbn in *; eauto.
Qed.

Definition prd_sup {A B : dcpo} (D : prod A B -> SProp) (d : directed prd_rel D) : prod A B :=
  pair (dcpo_sup A _ (directed_fst D d)) (dcpo_sup B _ (directed_snd D d)).

Program Definition Prd (A B : dcpo) : dcpo := Build_dcpo (prod A B) prd_rel prd_sup _.
Next Obligation.
intros A B; split.
+ intros [x y]; split; eapply dcpo_refl, dcpo_spc.
+ intros [x1 y1] [x2 y2] [x3 y3] [] []; cbn in *; split; eapply dcpo_transitivity; try eassumption; eapply dcpo_spc.
+ intros [x1 y1] [x2 y2] [] []; cbn in *; constructor.
  assert (Hx : x1 = x2).
  { eapply unbox, dcpo_irfl; try eassumption; eapply dcpo_spc. }
  assert (Hy : y1 = y2).
  { eapply unbox, dcpo_irfl; try eassumption; eapply dcpo_spc. }
  now subst.
+ intros D d; split.
  - intros [x y] Hxy; split; cbn.
    * now apply dcpo_sup_intro, (maprel_intro _ fst (pair x y)).
    * now apply dcpo_sup_intro, (maprel_intro _ (@snd _ (fun _ => _)) (pair x y)).
  - intros [x y] Hxy; split; cbn.
    * apply dcpo_sup_elim; intros ? [[x' y'] ? ?]; subst; cbn.
      now apply (Hxy (pair x' y')).
    * apply dcpo_sup_elim; intros ? [[x' y'] ? ?]; subst; cbn.
      now apply (Hxy (pair x' y')).
Qed.

Program Definition Fst {A B : dcpo} : Prd A B → A := {| arr_fun := fun p => p.(fst) |}.
Next Obligation.
intros A B; unshelve econstructor.
+ intros [] [] H; cbn in *; apply H.
+ intros D d HD; cbn.
  now apply dcpo_refl_elim.
Qed.

Program Definition Snd {A B : dcpo} : Prd A B → B := {| arr_fun := fun p => p.(snd) |}.
Next Obligation.
intros A B; unshelve econstructor.
+ intros [] [] H; cbn in *; apply H.
+ intros D d HD; cbn.
  now apply dcpo_refl_elim.
Qed.

Program Definition Dup {Γ A B : dcpo} (f : Γ → A) (g : Γ → B) : Γ → Prd A B :=
  Build_arr_car Γ (Prd A B) (fun γ => pair (f γ) (g γ)) _.
Next Obligation.
intros; unshelve econstructor.
+ intros γ γ' Hγ; split; cbn; [apply f|apply g]; assumption.
+ intros D d Hd; split; cbn.
  - rewrite continuous_sup; [|assumption].
    apply dcpo_sup_elim; intros ? [γ -> Hγ].
    apply dcpo_sup_intro; exists (pair (f γ) (g γ)); [reflexivity|].
    now exists γ.
  - rewrite continuous_sup; [|assumption].
    apply dcpo_sup_elim; intros ? [γ -> Hγ].
    apply dcpo_sup_intro; exists (pair (f γ) (g γ)); [reflexivity|].
    now exists γ.
Qed.

Program Definition Top : dcpo := Build_dcpo unit (fun _ _ => True) (fun _ _ => tt) _.
Next Obligation.
split; try now constructor.
+ intros [] [] _ _; repeat constructor.
Qed.

(*
Program Definition Ω : dcpo := Build_dcpo SProp (fun A B => A -> B) (fun D d => Box (subset SProp (fun P => and P (D P)))) _.
Next Obligation.
split.
+ intros; auto.
+ intros; auto.
+ admit.
+ intros D d; split.
  - intros P HP p.
    constructor; now exists P.
  - intros P HP [[Q [HQ]]].
    eapply HP; eassumption.

Definition open (A : dpco) (U : A -> SProp) : SProp :=
  forall D (d : directed (dcpo_rel D) D), iff (U (dcpo_sup D d)) ()
*)

Program Definition Lam {A B C : dcpo} (f : Arr (Prd A B) C) : Arr A (Arr B C) :=
  {| arr_fun := fun x => {| arr_fun := fun y => f (pair x y) |} |}.
Next Obligation.
intros; unshelve econstructor.
+ intros y1 y2 Hy.
  apply dcpo_arr_monotonous.
  constructor; cbn; [|assumption].
  eapply dcpo_refl, A.
+ intros DB db yd.
  pose (D := fun (p : prod A B) => and (Box (p.(fst) = x)) (DB p.(snd))).
  assert (d : directed (dcpo_rel (Prd A B)) D).
  { intros [x1 y1] [x2 y2] [[] d1] [[] d2]; cbn in *; subst x1 x2.
    destruct (db y1 y2 d1 d2) as [y [Hy]].
    exists (pair x y); repeat constructor; cbn; first [apply Hy|assumption|eapply dcpo_refl, A]. }
  let t := match goal with [ |- dcpo_rel _ (_ ?t) _ ] => t end in
  replace t with (dcpo_sup (Prd A B) D d).
  - rewrite continuous_sup.
    apply dcpo_refl_elim, dcpo_sup_ext; intros z; split.
    * intros [[x0 y0] ? [[] ?]]; cbn in *; subst.
      eexists y0; auto using Inj.
    * intros [y0 ? ?]; subst.
      now exists (pair x y0).
    * destruct yd as [yd Hyd]; exists (pair x yd); split; now auto using Box.
  - cbn; unfold prd_sup; f_equal.
    * apply dcpo_refl_intro.
      { apply dcpo_sup_elim; intros x' [[x0 y0] ? [[]]]; cbn in *; subst.
        eapply dcpo_refl, A. }
      { apply dcpo_sup_intro.
        destruct yd as [yd Hyd]; now exists (pair x yd). }
    * apply dcpo_sup_ext; intros y; split.
      { intros [[x0 y0] ? [? ?]]; subst; cbn in *; assumption. }
      { intros Hy; exists (pair x y); cbn; [reflexivity|].
        constructor; cbn; auto using Box. }
Qed.

Next Obligation.
intros; unshelve econstructor.
+ intros x1 x2 Hx y; cbn.
  apply dcpo_arr_monotonous.
  constructor; cbn; [assumption|].
  eapply dcpo_refl, B.
+ intros DA da xd y; cbn.
  pose (D := fun (p : prod A B) => and (DA p.(fst)) (Box (p.(snd) = y))).
  assert (d : directed (dcpo_rel (Prd A B)) D).
  { intros [x1 y1] [x2 y2] [d1 []] [d2 []]; cbn in *; subst y1 y2.
    destruct (da x1 x2 d1 d2) as [x [Hx]].
    exists (pair x y); repeat constructor; cbn; first [apply Hx|assumption|eapply dcpo_refl, B]. }
  let t := match goal with [ |- dcpo_rel _ (_ ?t) _ ] => t end in
  replace t with (dcpo_sup (Prd A B) D d).
  - rewrite continuous_sup.
    apply dcpo_refl_elim, dcpo_sup_ext; intros z; split.
    * intros [[x0 y0] ? [? []]]; cbn in *; subst.
      unfold aprel; apply maprel_bind_l; cbn.
      now exists x0.
    * intros [g -> [x ->]].
      exists (pair x y); [reflexivity|].
      split; auto using Box.
    * destruct xd as [x xd].
      now exists (pair x y).
  - cbn; unfold prd_sup; f_equal.
    * apply dcpo_sup_ext; intros x; split.
      { intros [[x0 y0] ? [? ?]]; subst; cbn in *; assumption. }
      { intros Hy; exists (pair x y); cbn; [reflexivity|].
        constructor; cbn; auto using Box. }
    * apply dcpo_refl_intro.
      { apply dcpo_sup_elim; intros x' [[x0 y0] ? [? []]]; cbn in *; subst.
        eapply dcpo_refl, B. }
      { apply dcpo_sup_intro.
        destruct xd as [xd Hxd]; now exists (pair xd y). }
Qed.

Lemma maprel_fun_ext : forall A B P f g y, (forall x, f x = g x) ->
  iff (@maprel A B P f y) (@maprel A B P g y).
Proof.
intros * H; apply funext in H; subst; apply iff_reflexivity.
Qed.

Lemma inhabited_maprel : forall {A B} {D : A -> SProp} {f : A -> B}, exist A D -> exist B (maprel D f).
Proof.
intros * [x d]; exists (f x).
now apply maprel_intro.
Qed.

Lemma app_continuous : forall {Γ A B : dcpo} (f : Γ → A → B) (x : Γ → A), continuous (fun γ : Γ => f γ (x γ)).
Proof.
intros; unshelve econstructor.
+ intros γ1 γ2 Hγ.
  destruct f as [f [Hf Hfs]]; cbn in *; clear Hfs.
  assert (dcpo_rel A (x γ1) (x γ2)) by now apply x.
  apply arr_rel_app.
  - now apply Hf.
  - now apply x.
+ intros D d xd.
  repeat (rewrite continuous_sup; [|assumption]); cbn; unfold aprel; cbn.
  let P := match goal with [ |- dcpo_rel _ (⊔ ?P) _ ] => P end in
  unshelve erewrite dcpo_sup_ext' with (D1 := P) (D2 := maprel D (fun γ => _)) (H := maprel_bind_l _ _ _).
  assert (Hm : forall γ : Γ, monotonous (dcpo_rel Γ) (dcpo_rel B) (fun γ' => f γ (x γ'))).
  { intros γ γ' γ'' Hγ.
    apply (dcpo_arr_monotonous (f γ)).
    now apply (dcpo_arr_monotonous x). }
  assert (dm : forall γ : Γ, directed (dcpo_rel B) (maprel D (fun γ' => f γ (x γ')))).
  { intros; eapply directed_maprel; eauto. }
  let q := match goal with [ |- context[ dcpo_sup _ (maprel D ?f) ?p ] ] => p end in
  set (p := q); clearbody p.
  let g := match goal with [ |- context[ dcpo_sup _ (maprel D ?f) _ ] ] => f end in
  assert (Hrw : g = (fun γ : Γ => dcpo_sup _ (maprel D (fun γ' => f γ (x γ'))) (dm γ))).
  { apply funext; intros γ.
    rewrite continuous_sup with (f := f γ); [|now apply inhabited_maprel].
    apply dcpo_sup_ext; intros y; split.
    + intros [a -> [γ' ->]]; now exists γ'.
    + intros [γ' ->].
      exists (x γ'); [reflexivity|].
      now exists γ'. }
  revert p; rewrite Hrw; intros p; clear Hrw.
  apply dcpo_sup_elim; intros y [γ -> ?].
  apply dcpo_sup_elim; intros y' [γ' -> ?].
  destruct (d γ γ') as [γ'' Hγ'']; try assumption.
  apply dcpo_transitivity with (f γ (x γ'')).
  { apply dcpo_arr_monotonous, dcpo_arr_monotonous, Hγ''. }
  apply dcpo_transitivity with (f γ'' (x γ'')).
  { apply (dcpo_arr_monotonous f), Hγ''. }
  apply dcpo_sup_intro.
  exists γ''; [reflexivity|apply Hγ''].
Qed.

Program Definition App {Γ A B : dcpo} (f : Arr Γ (Arr A B)) (x : Arr Γ A) : Arr Γ B :=
  {| arr_fun := fun γ => f γ (x γ) |}.
Next Obligation.
intros; apply app_continuous.
Qed.

Definition continuous_alt {A B : dcpo} (f : A -> B) :=
  forall (V : Arr B (Flat unit)), @continuous A (Flat unit) (fun x => V (f x)).

Program Definition cone {A : dcpo} (x : A) : Arr A (Flat unit) :=
  {| arr_fun := fun y =>
    match classical (subset unit (fun _ => dcpo_rel A y x)) with inl _ => None | inr _ => Some tt end |}.
Next Obligation.
intros A x₀; unshelve econstructor.
+ intros x x' Hx.
  repeat destruct classical as [[]|]; try now constructor.
  elim f; exists tt.
  now apply dcpo_transitivity with x'.
+ intros D d xd.
  assert (Hmin : forall x : Flat unit, dcpo_rel (Flat unit) None x).
  { destruct x; constructor. }
  assert (Hmax : forall x : Flat unit, dcpo_rel (Flat unit) x (Some tt)).
  { destruct x as [[]|]; constructor. }
  destruct classical as [[]|Hc]; [auto|].
  apply dcpo_sup_intro, absurdum; intros Hk.
  elim Hc; exists tt; apply dcpo_sup_elim.
  intros x Hx; apply absurdum; intros Hk'; elim Hk.
  exists x; [|assumption].
  destruct classical as [[]|]; auto.
  now elim Hk'.
Qed.

Lemma continuous_alt_monotonous : forall {A B : dcpo} (f : A -> B),
  continuous_alt f -> monotonous (dcpo_rel A) (dcpo_rel B) f.
Proof.
intros A B f Hf x x' Hx.
specialize (Hf (cone (f x'))).
apply Hf in Hx; cbn in Hx.
destruct classical as [[]|]; [auto|].
destruct classical as [[]|Hk]; [inversion Hx|].
elim Hk; exists tt; now apply dcpo_refl_elim.
Qed.

Lemma continuous_alt_equiv : forall {A B : dcpo} (f : A -> B),
  iff (continuous f) (continuous_alt f).
Proof.
intros A B f; split; intros Hf.
+ intros V; apply continuous_comp; eauto.
  apply arr_spc.
+ unshelve econstructor.
  - now apply continuous_alt_monotonous.
  - intros D d xd.
    match goal with [ |- context [dcpo_sup B (maprel D f) ?p0] ] => set (db := p0) end; clearbody db.
    specialize (Hf (cone (dcpo_sup _ _ db))).
    destruct Hf as [Hfm Hfc].
    specialize (Hfc D d xd); cbn in Hfc.
    destruct classical as [[]|Hsup]; [assumption|].
    unfold flat_sup in Hfc.
    destruct classical as [[[] [[x Hx]]]|]; [|inversion Hfc]; cbn in Hfc.
    destruct classical as [|Hdx]; [congruence|].
    elim Hdx; constructor; [constructor|].
    apply dcpo_sup_intro; now exists x.
Qed.

Inductive is_chain {A : dcpo} (f : A -> A) : A -> SProp :=
| is_chain_bot : is_chain f (dcpo_bot A)
| is_chain_cmp : forall x, is_chain f x -> is_chain f (f x).

Lemma directed_chain : forall {A : dcpo} (f : Arr A A),
  directed (dcpo_rel A) (fun x => is_chain f x).
Proof.
intros A f x y Hx Hy; revert y Hy.
induction Hx.
+ intros y Hy. exists y; constructor; auto.
  - apply dcpo_bot_spec.
  - eapply dcpo_refl, A.
+ intros y Hy.
  destruct Hy as [|y Hy].
  - exists (f x); constructor; auto.
    * now constructor.
    * eapply dcpo_refl, A.
    * apply dcpo_bot_spec.
  - destruct (IHHx y Hy) as [ω [Hω Hxω Hyω]].
    exists (f ω); econstructor.
    * now constructor.
    * now apply f.
    * now apply f.
Qed.

Lemma sup_chain_fix : forall {A : dcpo} (f : Arr A A),
  f (dcpo_sup A _ (directed_chain f)) = dcpo_sup A _ (directed_chain f).
Proof.
intros A f.
assert (exist A (fun x : A => is_chain f x)).
{ exists (dcpo_bot _); constructor. }
rewrite continuous_sup; [|assumption].
apply dcpo_refl_intro.
+ apply dcpo_sup_elim; intros x [x' -> Hx].
  apply dcpo_sup_intro; now constructor.
+ apply dcpo_sup_elim; intros x Hx.
  destruct Hx; [apply dcpo_bot_spec|].
  apply dcpo_sup_intro; now econstructor.
Qed.

Program Definition FixT {A : dcpo} : Arr (Arr A A) A :=
  {| arr_fun := fun f => dcpo_sup A _ (directed_chain f) |}.
Next Obligation.
intros; unshelve econstructor.
+ intros f f' Hf.
  apply dcpo_sup_elim; intros ω Hω.
  assert (H : exist A (fun ω' => and (is_chain f' ω') (dcpo_rel A ω ω'))).
  { induction Hω as [|ω]; cbn in *.
    + exists (dcpo_bot _); split; [constructor|].
      eapply dcpo_refl, A.
    + destruct IHHω as [ω' [Hω' Hr]].
      exists (f' ω'); split; [now constructor|].
      apply dcpo_transitivity with (f ω').
      - now apply dcpo_arr_monotonous.
      - apply Hf. }
  destruct H as [ω' [Hω' ?]].
  apply dcpo_transitivity with ω'; [assumption|].
  now apply dcpo_sup_intro.
+ intros Df df fd.
  apply dcpo_sup_elim; intros ω Hω.
  induction Hω as [|ω]; cbn.
  - apply dcpo_bot_spec.
  - apply dcpo_sup_elim; intros ? [f -> Hf].
    apply (dcpo_arr_monotonous f) in IHHω.
    assert (Hd : exist A (maprel Df (fun f : Arr A A => dcpo_sup A _ (directed_chain f)))).
    { exists (f (dcpo_sup A _ (directed_chain f))).
      exists f; [|assumption].
      apply sup_chain_fix. }
    rewrite continuous_sup in IHHω; [|assumption].
    eapply dcpo_transitivity; [apply IHHω|].
    apply dcpo_sup_elim; intros ? [? -> [g -> Hg]].
    destruct (df f g Hf Hg) as [h [Hh ? ?]].
    apply dcpo_transitivity with (h (dcpo_sup _ (fun x => is_chain h x) (directed_chain _))).
    * apply arr_rel_app; [assumption|].
      apply dcpo_sup_elim; intros x Hx.
      induction Hx; [apply dcpo_bot_spec|].
      rewrite <- sup_chain_fix.
      now apply arr_rel_app.
    * apply dcpo_sup_intro.
      exists h; [|assumption].
      apply sup_chain_fix.
Qed.

Inductive sum_rel {A B} (RA : A -> A -> SProp) (RB : B -> B -> SProp) : option (A + B) -> option (A + B) -> SProp :=
| sum_rel_bot : forall s, sum_rel RA RB None s
| sum_rel_inl : forall x x', RA x x' -> sum_rel RA RB (Some (inl x)) (Some (inl x'))
| sum_rel_inr : forall y y', RB y y' -> sum_rel RA RB (Some (inr y)) (Some (inr y')).

Lemma directed_sum_inl : forall {A B RA RB} D,
  directed (@sum_rel A B RA RB) D -> directed RA (fun x => D (Some (inl x))).
Proof.
intros * H.
intros x x' Hx Hx'.
destruct (H (Some (inl x)) (Some (inl x'))) as [o [Ho Hox Hox']]; try assumption.
inversion Hox; subst; inversion Hox'; subst.
match type of Ho with D (Some (inl ?z)) => exists z; now split end.
Qed.

Lemma directed_sum_inr : forall {A B RA RB} D,
  directed (@sum_rel A B RA RB) D -> directed RB (fun y => D (Some (inr y))).
Proof.
intros * H.
intros x x' Hx Hx'.
destruct (H (Some (inr x)) (Some (inr x'))) as [o [Ho Hox Hox']]; try assumption.
inversion Hox; subst; inversion Hox'; subst.
match type of Ho with D (Some (inr ?z)) => exists z; now split end.
Qed.

Definition sum_sup {A B : dcpo} (D : option (A + B) -> SProp) (d : directed (sum_rel (dcpo_rel A) (dcpo_rel B)) D) : option (A + B) :=
  match classical (subset A (fun x => D (Some (inl x)))) with
  | inl _ => Some (inl (dcpo_sup A _ (directed_sum_inl D d)))
  | inr _ =>
    match classical (subset B (fun x => D (Some (inr x)))) with
    | inl _ => Some (inr (dcpo_sup B _ (directed_sum_inr D d)))
    | inr _ => None
    end
  end.

Program Definition Sum (A B : dcpo) : dcpo := {|
  dcpo_car := option (A + B);
  dcpo_rel := sum_rel (dcpo_rel A) (dcpo_rel B);
  dcpo_sup := sum_sup;
|}.
Next Obligation.
intros; split.
+ intros [[]|]; constructor; now apply dcpo_refl_elim.
+ intros * Hl Hr; inversion Hl; subst; try now constructor.
  - inversion Hr; subst; constructor.
    eapply dcpo_transitivity; now eauto.
  - inversion Hr; subst; constructor.
    eapply dcpo_transitivity; now eauto.
+ intros * Hl Hr; inversion Hl; subst.
  - inversion Hr; repeat constructor.
  - inversion Hr; subst; constructor; repeat f_equal.
    now apply dcpo_refl_intro.
  - inversion Hr; subst; constructor; repeat f_equal.
    now apply dcpo_refl_intro.
+ intros; split.
  - intros p Hp; unfold sum_sup.
    destruct classical as [[a Ha]|]; [|destruct classical as [[b Hb]|]].
    * destruct p as [p|]; [|constructor].
      pose proof (H := d _ _ Hp Ha).
      destruct H as [m [Hm Hl Hr]].
      inversion Hl; subst; inversion Hr; subst.
      constructor; now apply dcpo_sup_intro.
    * destruct p as [p|]; [|constructor].
      pose proof (H := d _ _ Hp Hb).
      destruct H as [m [Hm Hl Hr]].
      inversion Hl; subst; inversion Hr; subst.
      constructor; now apply dcpo_sup_intro.
    * destruct p as [[a|b]|]; try constructor; exfalso; eauto using subset, sum_rel.
  - intros p Hp; unfold sum_sup.
    destruct classical as [[a Ha]|]; [|destruct classical as [[b Hb]|]].
    * pose proof (H := Hp _ Ha); inversion H; subst.
      constructor; apply dcpo_sup_elim; intros.
      match goal with [ |- dcpo_rel A ?x ?y ] => enough (Hr : sum_rel (dcpo_rel A) (dcpo_rel B) (Some (inl x)) (Some (inl y))) by now inversion Hr end.
      now apply Hp.
    * pose proof (H := Hp _ Hb); inversion H; subst.
      constructor; apply dcpo_sup_elim; intros.
      match goal with [ |- dcpo_rel B ?x ?y ] => enough (Hr : sum_rel (dcpo_rel A) (dcpo_rel B) (Some (inr x)) (Some (inr y))) by now inversion Hr end.
      now apply Hp.
    * destruct p as [[a|b]|]; try constructor; exfalso; eauto using subset, sum_rel.
Qed.

(*
Program Definition Sum_recT {A B C : dcpo} (ul : A → C) (ur : B → C) : Sum A B → C :=
  {| arr_fun := fun s => match s with None => dcpo_bot _ | Some (inl x) => ul x | Some (inr y) => ur y end |}.
Next Obligation.
intros *; unshelve econstructor.
+ intros [[x|y]|] s Hs; inversion Hs; subst.
  - now apply ul.
  - now apply ur.
  - apply dcpo_bot_spec.
+ intros D d Hd; cbn; unfold sum_sup.
  destruct classical as [[x Hx]|kx]; [|destruct classical as [[y Hy]|ky]].
  - rewrite continuous_sup; [|now eexists; eauto].
    apply dcpo_sup_elim; intros ? [x' -> Hx'].
    destruct (d _ _ Hx Hx') as [s [? Hl Hr]].
    inversion Hr; subst.
    eapply dcpo_transitivity; [apply ul; eauto|].
    apply dcpo_sup_intro; eexists (Some (inl _)); [reflexivity|assumption].
  - rewrite continuous_sup; [|now eexists; eauto].
    apply dcpo_sup_elim; intros ? [y' -> Hy'].
    destruct (d _ _ Hy Hy') as [s [? Hl Hr]].
    inversion Hr; subst.
    eapply dcpo_transitivity; [apply ur; eauto|].
    apply dcpo_sup_intro; eexists (Some (inr _)); [reflexivity|assumption].
  - apply dcpo_bot_spec.
Qed.
*)

Program Definition Inl {Γ A B : dcpo} (x : Γ → A) : Γ → Sum A B :=
  {| arr_fun := fun γ => Some (inl (x γ)) |}.
Next Obligation.
intros; unshelve econstructor.
+ intros γ γ' Hγ; constructor; now apply x.
+ intros D d Hd.
  rewrite continuous_sup; [|assumption].
  cbn; unfold sum_sup.
  destruct classical as [[a [γ Ha]]|Ha]; [|destruct classical as [[b [γ Hb]]|Hb]].
  - constructor.
    apply dcpo_sup_elim; intros ? [γ' ->].
    apply dcpo_sup_intro; now exists γ'.
  - exfalso; congruence.
  - destruct Hd as [γ Hγ].
    elim Ha; exists (x γ); now exists γ.
Qed.

Program Definition Inr {Γ A B : dcpo} (y : Γ → B) : Γ → Sum A B :=
  {| arr_fun := fun γ => Some (inr (y γ)) |}.
Next Obligation.
intros; unshelve econstructor.
+ intros γ γ' Hγ; constructor; now apply y.
+ intros D d Hd.
  rewrite continuous_sup; [|assumption].
  cbn; unfold sum_sup.
  destruct classical as [[a [γ Ha]]|Ha]; [|destruct classical as [[b [γ Hb]]|Hb]].
  - exfalso; congruence.
  - constructor.
    apply dcpo_sup_elim; intros ? [γ' ->].
    apply dcpo_sup_intro; now exists γ'.
  - destruct Hd as [γ Hγ].
    elim Hb; exists (y γ); now exists γ.
Qed.

Program Definition Sum_rec {Γ A B C : dcpo}
  (ul : Γ → A → C) (ur : Γ → B → C) (s : Γ → Sum A B) : Γ → C :=
  {| arr_fun := fun γ => match s γ with None => dcpo_bot _ | Some (inl x) => ul γ x | Some (inr y) => ur γ y end |}.
Next Obligation.
intros *; unshelve econstructor.
+ intros γ γ' Hγ.
  unshelve epose proof (Hs := arr_rel_app s s γ γ' _ Hγ).
  { intros ?; now apply dcpo_refl_elim. }
  remember (s γ) as p; destruct p as [[x|y]|]; inversion Hs; subst.
  - apply arr_rel_app; [|assumption].
    apply (@arr_rel_app _ (Arr _ _)); [|assumption].
    intros ?; now apply dcpo_refl_elim.
  - apply arr_rel_app; [|assumption].
    apply (@arr_rel_app _ (Arr _ _)); [|assumption].
    intros ?; now apply dcpo_refl_elim.
  - apply dcpo_bot_spec.
+ intros D d Hd; cbn.
  repeat (rewrite continuous_sup; [|assumption]).
  cbn; unfold sum_sup.
  destruct classical as [[x Hx]|kx]; [|destruct classical as [[y Hy]|ky]].
  - apply dcpo_sup_elim; intros ? [f -> [γ -> Hγ]].
    rewrite continuous_sup; [|now eexists; eauto].
    apply dcpo_sup_elim; intros ? [x' -> [γ' Heq Hγ']].
    destruct (d _ _ Hγ Hγ') as [γ'' [? Hl Hr]].
    unshelve epose proof (Hs := arr_rel_app s s γ' γ'' _ Hr).
    { intros ?; now apply dcpo_refl_elim. }
    rewrite <- Heq in Hs; inversion Hs; subst.
    match goal with [ H : Some (inl ?x) = _ γ'' |- _ ] => rename x into x'' end.
    eapply dcpo_transitivity with (ul γ'' x'').
    { apply arr_rel_app; [|assumption]; now apply ul. }
    apply dcpo_sup_intro; exists γ''; [|assumption].
    match goal with [ H : Some (inl ?x) = _ γ'' |- _ ] => now rewrite <- H end.
  - apply dcpo_sup_elim; intros ? [f -> [γ -> Hγ]].
    rewrite continuous_sup; [|now eexists; eauto].
    apply dcpo_sup_elim; intros ? [y' -> [γ' Heq Hγ']].
    destruct (d _ _ Hγ Hγ') as [γ'' [? Hl Hr]].
    unshelve epose proof (Hs := arr_rel_app s s γ' γ'' _ Hr).
    { intros ?; now apply dcpo_refl_elim. }
    rewrite <- Heq in Hs; inversion Hs; subst.
    match goal with [ H : Some (inr ?y) = _ γ'' |- _ ] => rename y into y'' end.
    eapply dcpo_transitivity with (ur γ'' y'').
    { apply arr_rel_app; [|assumption]; now apply ur. }
    apply dcpo_sup_intro; exists γ''; [|assumption].
    match goal with [ H : Some (inr ?x) = _ γ'' |- _ ] => now rewrite <- H end.
  - apply dcpo_bot_spec.
Qed.

Program Definition Fix {Γ A : dcpo} (f : Γ → A → A) : Γ → A :=
  {| arr_fun := fun γ => FixT (f γ) |}.
Next Obligation.
intros; apply continuous_comp.
+ apply f.
+ apply FixT.
Qed.

Program Definition Let {Γ A : dcpo} {X : Type} (v : Γ → Flat X) (f : X -> Γ → A) : Γ → A :=
  App (Lam {| arr_fun := fun (γ : Prd Γ (Flat X))  => match snd γ with None => dcpo_bot _ | Some x => f x (fst γ) end |}) v.
Next Obligation.
intros; unshelve econstructor.
+ intros [γ x] [γ' x'] [Hγ Hx].
  destruct x as [x|]; [|apply dcpo_bot_spec].
  cbn [fst snd] in *.
  destruct x' as [x'|]; [|now inversion Hx].
  assert (Heq : x = x'); [|subst x'].
  { apply unbox; inversion Hx; repeat constructor. }
  now apply f.
+ intros D d Hd; cbn; unfold flat_sup.
  destruct classical as [[? [[[γ x] Heq]]]|Hx]; cbn in *; [|apply dcpo_bot_spec].
  destruct x as [x|]; [|congruence].
  injection Heq; intros ->.
  assert (exist Γ (maprel D fst)).
  { exists γ; now exists (pair γ (Some x)). }
  rewrite continuous_sup; [|assumption].
  apply dcpo_sup_elim; intros ? [? -> [[γ' x'] ->]]; cbn.
  edestruct (d (pair γ (Some x)) (pair γ' x')) as [[γ'' x''] [? [? Hl] []]]; try assumption; cbn in *.
  destruct x'' as [x''|]; [|now inversion Hl].
  assert (Hrw : x = x''); [|subst x''].
  { apply unbox; inversion Hl; subst; repeat constructor. }
  apply dcpo_transitivity with (f x γ''); [now apply f|].
  apply dcpo_sup_intro; exists (pair γ'' (Some x)); [|assumption].
  reflexivity.
Qed.

(* upd (s : ℕ → 1 + A) (n : ℕ) (v : A) : ℕ → 1 + A := fun m => if m == n then Some v else s m *)

Definition Upd {Γ A : dcpo} (s : Γ → ℕ → Sum Top A) (n : Γ → ℕ) (v : Γ → A) : Γ → ℕ → Sum Top A :=
  Lam (Let (Comp Fst n) (fun n₀ => Let Snd (fun m₀ => if Nat.eqb m₀ n₀ then Inr (Comp Fst v) else App (Comp Fst s) Snd))).

(*

ur : ((ℕ → A + (A → ℕ)) → ℕ) → (ℕ → 1 + A) → ℕ
ur φ α ≡ φ (fun n => match α n with None => inl (fun y => ur φ (α ⊕ ⟨n ↦ y⟩)) | Some x => inr x end)

*)

Definition barrec {Γ A : dcpo} : Γ → ((ℕ → Sum A (A → ℕ)) → ℕ) → (ℕ → Sum Top A) → ℕ.
Proof.
refine (Lam (Fix (Lam (Lam (App (Comp Fst (Comp Fst Snd)) (Lam _)))))).
refine (Sum_rec (Lam (Inr _)) (Lam (Inl Snd)) (App (Comp Fst Snd) Snd)).
refine (Lam (App (Comp Fst (Comp Fst (Comp Fst (Comp Fst Snd)))) _)).
refine (Upd (Comp Fst (Comp Fst (Comp Fst Snd))) (Comp Fst (Comp Fst Snd)) Snd).
Defined.

(** Proof of totality *)

Inductive typ :=
| Tflat : Type -> typ
| Tarr : typ -> typ -> typ
| Ttop : typ
| Tprd : typ -> typ -> typ
| Tsum : typ -> typ -> typ.

Fixpoint Teval (σ : typ) : dcpo :=
match σ with
| Tflat A => Flat A
| Tarr σ τ => Arr (Teval σ) (Teval τ)
| Ttop => Top
| Tprd σ τ => Prd (Teval σ) (Teval τ)
| Tsum σ τ => Sum (Teval σ) (Teval τ)
end.

Inductive flat_tot {A} : Flat A -> SProp :=
| flat_tot_Some : forall x, flat_tot (Some x).

Inductive sum_tot {A B : dcpo} (TA : A -> SProp) (TB : B -> SProp) : Sum A B -> SProp :=
| sum_tot_inl : forall x, TA x -> sum_tot TA TB (Some (inl x))
| sum_tot_inr : forall y, TB y -> sum_tot TA TB (Some (inr y)).

Fixpoint Ttotal (σ : typ) : Teval σ -> SProp :=
match σ return Teval σ -> SProp with
| Tflat _ => flat_tot
| Tarr σ τ => fun f => forall x : Teval σ, Ttotal σ x -> Ttotal τ (f x)
| Ttop => fun _ => True
| Tprd σ τ => fun p => and (Ttotal σ (fst p)) (Ttotal τ (snd p))
| Tsum σ τ => sum_tot (Ttotal σ) (Ttotal τ)
end.

Definition Tnat := Tflat nat.

Lemma total_flat_sup_intro : forall A D (d : directed (@flat_rel A) D),
  exist A (fun x => D (Some x)) ->
  Ttotal (Tflat A) (dcpo_sup (Flat A) D d).
Proof.
intros * [x Hx]; cbn.
unfold flat_sup; destruct classical as [[x' [Hx']]|Hx'].
+ constructor.
+ elim Hx'; repeat econstructor; eauto.
Qed.

Lemma total_flat_FixT_intro : forall (σ : typ) (A : Type)
  (f : (Teval σ → Flat A) → (Teval σ → Flat A)) (x : Teval σ),
  (exist nat (fun n => Nat.iter n f (dcpo_bot _) x = None -> False)) ->
  Ttotal (Tflat A) (FixT f x).
Proof.
intros * [n Hn]; cbn.
unfold flat_sup; destruct classical as [[]|Hk].
+ constructor.
+ remember (Nat.iter n f (dcpo_bot _) x) as v; destruct v as [v|]; [|now elim Hn].
  elim Hk; exists v; constructor.
  exists (Nat.iter n f (dcpo_bot _)).
  - symmetry; now apply unbox.
  - clear; induction n; cbn; constructor; assumption.
Qed.

Program Definition is_strict {A} : Flat A → Flat unit :=
  {| arr_fun := fun x => match x with None => None | Some _ => Some tt end |}.
Next Obligation.
intros A; unshelve econstructor.
+ intros x x' Hx; induction Hx; constructor.
+ intros D d Hd; cbn; unfold flat_sup.
  destruct classical as [[x [Hx]]|Hx]; destruct classical as [[y [Hy]]|Hy]; cbn; try constructor.
  - destruct Hy as [[] Hrw]; [|congruence].
    rewrite Hrw; constructor.
  - elim Hy; exists tt; constructor.
    now exists (Some x).
Qed.

Lemma total_barrec : forall (Γ : dcpo) (σ : typ) (γ : Γ),
  Ttotal (Tarr (Tarr (Tarr Tnat (Tsum σ (Tarr σ Tnat))) Tnat) (Tarr (Tarr Tnat (Tsum Ttop σ)) Tnat)) (@barrec Γ (Teval σ) γ).
Proof.
intros Γ σ γ φ φε α αε; cbn in φ, α.
unfold barrec.
assert (Hφ : continuous_alt φ).
{ apply continuous_alt_equiv, φ. }
specialize (Hφ is_strict).
destruct Hφ as [Hφm Hφs].
unfold Lam at 1; cbn [arr_fun].
unfold Fix at 1; cbn [arr_fun].
refine (total_flat_FixT_intro (Tarr Tnat (Tsum Ttop σ)) _ _ _ _).
match goal with |- context [Nat.iter _ (arr_fun _ _ ?f)] => set (Φ := f) end.
(* unfold Lam at 1; cbn [arr_fun]. *)
(* match goal with |- context [Nat.iter _ ?f] => set (Φ := f) end. *)
apply absurdum; intros H.
assert (HΦ : forall n : nat, Nat.iter n Φ (dcpo_bot _) α = None).
{ intros n; match goal with |- ?P = None => remember P as p end.
  destruct p as [p|]; [|trivial].
  elim H; exists n; intros Hn.
  enough (Some p = None) by congruence.
  rewrite <- Hn, Heqp; reflexivity. }
clear H.
(* pose (D (f : ℕ → Sum (Teval σ) (Teval σ → ℕ)) := _). *)


(* unfold App at 2; cbn [arr_fun]. *)
(*
cbn [Lam App Sum_rec arr_fun].
cbn [Comp Fst Snd arr_fun fst snd].
cbn [Inl Snd arr_fun snd fst].
cbn [Inr Snd arr_fun snd fst].
cbn [Lam App Sum_rec arr_fun].
cbn [Comp Fst Snd arr_fun fst snd].


apply absurdum; intros H.
unfold Lam at 1 in H; cbn [arr_fun] in H.
cbn [Lam App arr_fun] in H.
let t := match type of H with context [Lam (App ?f _)] => f end in set (X := t) in *.

cbn in X.
change (Comp Fst (Comp Fst Snd)) in H.

unfold Lam at 1 in H; cbn [arr_fun] in H.
*)
Abort.
