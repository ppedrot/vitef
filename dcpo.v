Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive Box@{i} (A : Type@{i}) : SProp := box : A -> Box A.
Inductive Inj@{i} (A : SProp) : Type@{i} := inj : A -> Inj A.
Inductive False : SProp :=.

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
    subset A D ->
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
  subset A D ->
  (f (A.(dcpo_sup) D d)) = (B.(dcpo_sup) (maprel D f) (directed_maprel f.(arr_spc).(cont_mono) d)).
Proof.
intros.
eapply unbox, dcpo_irfl; [apply dcpo_spc| |].
+ now apply cont_sup.
+ apply monotonous_sup_le.
Qed.

Lemma dcpo_arr_monotonous : forall {A B : dcpo} (f : arr_car A B), monotonous (dcpo_rel A) (dcpo_rel B) f.
Proof.
intros; apply cont_mono, arr_spc.
Qed.

Definition arr_rel {A B : dcpo} (f g : arr_car A B) := forall x : A, dcpo_rel B (f x) (g x).

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

Lemma dcpo_sup_ext : forall (A : dcpo) D1 D2
  (d1 : directed (dcpo_rel A) D1) (d2 : directed (dcpo_rel A) D2),
  (forall x, iff (D1 x) (D2 x)) -> dcpo_sup A D1 d1 = dcpo_sup A D2 d2.
Proof.
intros * H.
apply unbox; eapply dcpo_irfl; [apply A|..].
+ apply dcpo_sup_monotonous; intros; now apply H.
+ apply dcpo_sup_monotonous; intros; now apply H.
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

Lemma continuous_alt : forall {A B : dcpo} (f : A -> B),
  iff (continuous f) (continuous f).
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

Lemma maprel_fun_ext : forall A B P f g y, (forall x, f x = g x) ->
  iff (@maprel A B P f y) (@maprel A B P g y).
Proof.
intros * H; apply funext in H; subst; apply iff_reflexivity.
Qed.

Lemma maprel_bind_l : forall {A B C} P (f : A -> B) (g : B -> C) (z : C), iff (maprel (maprel P f) g z) (maprel P (fun x => g (f x)) z).
Proof.
intros; split.
+ intros [y ? Hy]; subst.
  destruct Hy as [x ? Hx]; subst.
  now exists x.
+ intros [x ? ?]; subst.
  exists (f x); [reflexivity|].
  exists x; auto using Inj.
Qed.

Program Definition App {Γ A B : dcpo} (f : Arr Γ (Arr A B)) (x : Arr Γ A) : Arr Γ B :=
  {| arr_fun := fun γ => f γ (x γ) |}.
Next Obligation.
intros; unshelve econstructor.
+ intros γ1 γ2 Hγ.
  destruct f as [f [Hf Hfs]]; cbn in *; clear Hfs.
  assert (dcpo_rel A (x γ1) (x γ2)) by now apply x.
  eapply dcpo_transitivity with (y := (f γ1 (x γ2))).
  - now apply (f γ1).
  - now apply Hf.
+ intros D d xd.
  repeat (rewrite continuous_sup; [|assumption]); cbn; unfold aprel; cbn.
  apply dcpo_refl_elim.
  apply dcpo_sup_ext; intros y.
  eapply iff_transitivity; [apply maprel_bind_l|]; cbn.
  eapply iff_transitivity.
  { apply maprel_fun_ext; intros γ.
    rewrite continuous_sup; [|destruct xd as [γ0]; exists (x γ0); eexists; eauto using Inj].
    apply dcpo_sup_ext, maprel_bind_l. }
  split.
  - intros [γ ? ?]; subst.
    eexists γ.
Abort.

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
