Require Import Lia.

Set Primitive Projections.

Axiom pi : forall (P : Prop) (p q : P), p = q.

Axiom funext : forall (A : Type) (B : A -> Type)
  (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g.

CoInductive ℙ := mkℙ { hd : bool; tl : ℙ }.

Axiom ℙ_eta : forall s, s = mkℙ s.(hd) s.(tl).

Fixpoint take (n : nat) (α : ℙ) : list bool :=
match n with
| 0 => nil
| S n => cons α.(hd) (take n α.(tl))
end.

Fixpoint skip (n : nat) (α : ℙ) : ℙ :=
match n with
| 0 => α
| S n => skip n α.(tl)
end.

Fixpoint nth (α : ℙ) (n : nat) : bool :=
match n with
| 0 => α.(hd)
| S n => nth α.(tl) n
end.

Fixpoint app (s : list bool) (α : ℙ) : ℙ :=
match s with
| nil => α
| cons b s => mkℙ b (app s α)
end.

Inductive eqn (α β : ℙ) : nat -> Prop :=
| eqn_0 : eqn α β 0
| eqn_S : forall n, α.(hd) = β.(hd) -> eqn α.(tl) β.(tl) n -> eqn α β (S n).

Lemma eqn_le : forall α β n m, m <= n -> eqn α β n -> eqn α β m.
Proof.
intros α β n m H He; revert m H.
induction He; intros m Hle.
+ inversion Hle; constructor.
+ destruct m as [|m].
  - constructor.
  - constructor; [assumption|apply IHHe, le_S_n; assumption].
Qed.

Definition act {X : Type} (p : ℙ -> ℙ) (x : ℙ -> X) : ℙ -> X := fun α => x (p α).

Notation "p · x" := (act p x) (at level 30, right associativity).

Definition merge {X : Type} (x y : ℙ -> X) : ℙ -> X :=
  fun α => if α.(hd) then x α.(tl) else y α.(tl).

Definition λ₀ : ℙ -> ℙ := fun α => mkℙ true α.
Definition ρ₀ : ℙ -> ℙ := fun α => mkℙ false α.

Inductive cover {X} (P : (ℙ -> X) -> Prop) (x : ℙ -> X) : Prop :=
| cov_ret : P x -> cover P x
| cov_bnd : cover P (act λ₀ x) -> cover P (act ρ₀ x) -> cover P x.

Definition isContinuous (p : ℙ -> ℙ) :=
  forall m : nat, exists n : nat, forall α β : ℙ, eqn α β n -> eqn (p α) (p β) m.

Inductive extends : nat -> (ℙ -> ℙ) -> Prop :=
| extends_refl : forall p, isContinuous p -> extends 0 p
| extends_λ : forall n p, extends n p -> extends (S n) (act λ₀ p)
| extends_ρ : forall n p, extends n p -> extends (S n) (act ρ₀ p).

Definition isContinuous' (p : ℙ -> ℙ) :=
  forall m : nat, exists n : nat,
    forall s : list bool, length s = n ->
      exists p₀ : ℙ -> ℙ, exists s₀ : list bool,
        isContinuous p₀ /\ length s₀ = m /\ act (app s) p = act p₀ (app s₀).

Lemma merge_LR : forall {X : Type} (x : ℙ -> X), merge (act λ₀ x) (act ρ₀ x) = x.
Proof.
intros X x.
apply funext; intros α.
unfold merge, λ₀, ρ₀; simpl.
rewrite (ℙ_eta α); simpl.
destruct (hd α); reflexivity.
Qed.

Lemma L_merge : forall {X : Type} (x y : ℙ -> X), act λ₀ (merge x y) = x.
Proof.
reflexivity.
Qed.

Lemma R_merge : forall {X : Type} (x y : ℙ -> X), act ρ₀ (merge x y) = y.
Proof.
reflexivity.
Qed.

Lemma length_take : forall n s, length (take n s) = n.
Proof.
induction n; intros s; simpl; intuition eauto.
Qed.

Lemma eqn_nth : forall α β n, eqn α β (S n) -> nth α n = nth β n.
Proof.
fix F 4; intros α β n H.
refine (
match H in eqn _ _ n return
  match n with O => True | S n => nth α n = nth β n end
with
| eqn_0 _ _ => I
| eqn_S _ _ n h t => _
end).
destruct n as [|n].
+ assumption.
+ simpl; apply F; assumption.
Qed.

Lemma eqn_take : forall α β n, eqn α β n -> take n α = take n β.
Proof.
induction 1; simpl.
+ constructor.
+ f_equal; assumption.
Qed.

Lemma take_eqn : forall α β n, take n α = take n β -> eqn α β n.
Proof.
intros α β n; revert α β; induction n as [|n IHn]; intros α β H; simpl in *.
+ constructor.
+ constructor.
  - congruence.
  - apply IHn; congruence.
Qed.

Lemma take_skip : forall n s, app (take n s) (skip n s) = s.
Proof.
induction n; intros s; simpl.
+ reflexivity.
+ rewrite (IHn (tl s)), ℙ_eta; reflexivity.
Qed.

Lemma take_app : forall s α, take (length s) (app s α) = s.
Proof.
induction s as [|b s IHs]; intros α; simpl.
+ reflexivity.
+ f_equal; apply IHs.
Qed.

Lemma isContinuous_act : forall p q,
  isContinuous p -> isContinuous q -> isContinuous (act p q).
Proof.
intros p q Hp Hq m; unfold act.
destruct (Hq m) as [n Hn].
destruct (Hp n) as [l Hl].
exists l; intros α β H.
apply Hn, Hl, H.
Qed.

Lemma isContinuous_app : forall s, isContinuous (app s).
Proof.
intros s m; exists m.
revert m; induction s as [|b s]; intros m α β H; simpl.
+ assumption.
+ destruct m as [|m]; constructor; simpl; try reflexivity.
  apply IHs; eapply eqn_le; [|eassumption].
  repeat constructor.
Qed.

Lemma isContinuous_skip : forall n, isContinuous (skip n).
Proof.
intros s m.
exists (s + m); intros α β H.
revert m α β H; induction s as [|s IHs]; intros m α β H; simpl in *.
+ assumption.
+ inversion H; subst.
  apply IHs; assumption.
Qed.

Lemma isContinuous_1 : forall p, isContinuous p -> isContinuous' p.
Proof.
intros p Hp m.
destruct (Hp m) as [n Hn].
exists n; intros s Hs.
exists (fun α => skip m (p (app s α))).
exists (take m (p (app s (cofix ω := mkℙ true ω)))).
split; [|split].
+ change (isContinuous (act (act (app s) p) (skip m))).
  apply isContinuous_act; [apply isContinuous_act|].
  - apply isContinuous_app.
  - assumption.
  - apply isContinuous_skip.
+ apply length_take.
+ apply funext; intros α.
  unfold act.
  replace (take m (p (app s (cofix ω := mkℙ true ω)))) with (take m (p (app s α))).
  - rewrite take_skip; reflexivity.
  - apply eqn_take, Hn.
    rewrite <- Hs.
    apply take_eqn; rewrite !take_app; reflexivity.
Qed.

Lemma isContinuous_2 : forall p, isContinuous' p -> isContinuous p.
Proof.
intros p Hp m.
destruct (Hp m) as [n Hn].
exists n; intros α β H.
specialize (Hn (take n α) (length_take _ _)).
destruct Hn as [p₀ [s₀ [Hp₀ [Hs₀ He]]]].
apply take_eqn.
unfold act in He.
rewrite <- (take_skip n α).
rewrite <- (take_skip n β).
replace (take n β) with (take n α) by (apply eqn_take; assumption).
pose (Heα := f_equal (fun f => f (skip n α)) He).
pose (Heβ := f_equal (fun f => f (skip n β)) He).
simpl in *.
rewrite Heα, Heβ, <- Hs₀, !take_app; reflexivity.
Qed.

Record M := {
  hom : ℙ -> ℙ;
  spc : isContinuous hom;
}.

Coercion hom : M >-> Funclass.

Inductive D (A : Type) : Type :=
| η : A -> D A
| ask : forall (m : nat), D A -> D A -> D A.

Arguments η {_}.
Arguments ask {_}.

Definition one : M.
Proof.
exists (fun α => α).
intros m; exists m; intros α β h; exact h.
Defined.

Definition dot (p q : M) : M.
Proof.
exists (fun α => q (p α)).
apply isContinuous_act; apply spc.
Defined.

Definition λ : M.
Proof.
exists λ₀.
change (isContinuous (app (cons true nil))).
apply isContinuous_app.
Defined.

Definition ρ : M.
Proof.
exists ρ₀.
change (isContinuous (app (cons false nil))).
apply isContinuous_app.
Defined.

Record S := {
  car : Type;
  rel : (ℙ -> car) -> Prop;
  rel_ret : forall (x : car), rel (fun _ => x);
  rel_hom : forall x (p : M), rel x -> rel (p · x);
  rel_bnd : forall x, rel (act λ₀ x) -> rel (act ρ₀ x) -> rel x;
}.

Coercion car : S >-> Sortclass.

Lemma cover_rel : forall (X : S) (x : ℙ -> X), cover (rel X) x -> rel X x.
Proof.
induction 1.
+ assumption.
+ apply rel_bnd; assumption.
Qed.

Record Fun (X Y : S) := {
  fun_fun : X -> Y;
  fun_rel : forall (x : ℙ -> X), X.(rel) x -> Y.(rel) (fun α => fun_fun (x α));
}.

Arguments fun_fun {_ _}.
Arguments fun_rel {_ _}.

Coercion fun_fun : Fun >-> Funclass.

Definition Fun_bnd {X Y : S} (f : ℙ -> Fun X Y)
  (fl : forall (p : M) (x : ℙ -> X),
   rel X x -> rel Y (fun α : ℙ => (act λ₀ f) (p α) (x α)))
  (fr : forall (p : M) (x : ℙ -> X),
   rel X x -> rel Y (fun α : ℙ => (act ρ₀ f) (p α) (x α)))
  (p : M) (x : ℙ -> X) (xε : rel X x) : rel Y (fun α : ℙ => f (p α) (x α)).
Proof.
assert (Hp : isContinuous' p).
{ apply isContinuous_1; destruct p; assumption. }
destruct (Hp 1) as [m Hm]; clear Hp.
assert (Hs : forall s, length s = m -> exists (p₀ : ℙ -> ℙ),
  isContinuous p₀ /\ (app s · p = p₀ · λ₀ \/ app s · p = p₀ · ρ₀)).
{ intros s Hs. destruct (Hm s Hs) as [p₀ [s₀ [Hp₀ [Hs₀ He]]]].
  exists p₀; split; [assumption|].
  destruct s₀ as [|b s₀]; [exfalso; simpl in Hs₀; congruence|].
  destruct s₀ as [|? s₀]; [|exfalso; simpl in Hs₀; congruence].
  rewrite He; destruct b; simpl.
  + left; reflexivity.
  + right; reflexivity. }
clear Hm; revert p x xε Hs.
induction m as [|m IHm]; intros p x xε Hs.
- specialize (Hs nil eq_refl).
  destruct Hs as [p₀ [s₀ [He|He]]]; change (app nil · p) with (hom p) in He; rewrite He.
  * apply (fl (Build_M p₀ s₀)); assumption.
  * apply (fr (Build_M p₀ s₀)); assumption.
- apply rel_bnd; unfold act.
  * apply (IHm (dot λ p) (act λ₀ x)); [apply (rel_hom _ _ λ); assumption|].
    intros s Hs'.
    destruct (Hs (cons true s)) as [p₀ [Hp₀ He]]; [simpl; congruence|].
    exists p₀; split; [assumption|].
    { change (app s · dot λ p) with (app (true :: s) · p); assumption. }
  * apply (IHm (dot ρ p) (act ρ₀ x)); [apply (rel_hom _ _ ρ); assumption|].
    intros s Hs'.
    destruct (Hs (cons false s)) as [p₀ [Hp₀ He]]; [simpl; congruence|].
    exists p₀; split; [assumption|].
    { change (app s · dot ρ p) with (app (false :: s) · p); assumption. }
Qed.

Definition arrᶠ (X Y : S) : S.
Proof.
unshelve econstructor.
+ exact (Fun X Y).
+ refine (fun f => forall (p : M) (x : ℙ -> X), X.(rel) x -> Y.(rel) (fun α => f (p α) (x α))).
+ intros [f hf] _ x xε; refine (hf x xε).
+ simpl; intros f p fε q x xε.
  refine (fε (dot q p) x xε).
+ simpl. apply Fun_bnd.
Defined.

Definition isLocal {X} (x : ℙ -> X) :=
  exists m : nat, forall α β, eqn α β m -> x α = x β.

Definition Discᶠ (A : Type) : S.
Proof.
unshelve econstructor.
+ exact A.
+ refine isLocal.
+ simpl; intros n; exists 0; intros; reflexivity.
+ simpl; intros n p [m Hm].
  destruct (p.(spc) m) as [l Hl].
  exists l; intros α β H; apply Hm, Hl, H.
+ simpl. intros n [ml Hml] [mr Hmr].
  unfold act in *.
  exists (Datatypes.S (Nat.max ml mr)); intros α β H.
  rewrite (ℙ_eta α), (ℙ_eta β).
  replace (hd β) with (hd α).
  2:{ inversion H; assumption. }
  set (b := α.(hd)); set (α' := tl α); set (β' := tl β).
  assert (eqn α' β' (Nat.max ml mr)) by (inversion H; assumption).
  clearbody b α' β'.
  destruct b; [apply Hml|apply Hmr]; (eapply eqn_le; [|eassumption]); lia.
Defined.

Definition natᶠ : S := Discᶠ nat.

Definition boolᶠ : S := Discᶠ bool.

Lemma inj : (nat -> bool) -> arrᶠ natᶠ boolᶠ.
Proof.
intros f; unshelve econstructor; simpl.
+ exact f.
+ intros n [m Hm].
  exists m; intros α β H.
  f_equal; apply Hm, H.
Defined.

Lemma fan_spec : forall (f : arrᶠ (arrᶠ natᶠ boolᶠ) natᶠ),
  isLocal (fun α => f (inj (nth α))).
Proof.
intros [f fε]; simpl in *.
apply (fε (fun α => (inj (nth α)))).
intros p n [m Hm].
destruct (p.(spc) m) as [l Hl].
exists (Nat.max m l); intros α β H; simpl.
rewrite (Hm α β); [|eapply eqn_le; [|eassumption]; lia].
apply eqn_nth.
eapply eqn_le.
2:{ apply Hl. admit. }
Admitted.

Definition fanᶠ : arrᶠ (arrᶠ (arrᶠ natᶠ boolᶠ) natᶠ) natᶠ.
Proof.
unshelve econstructor; simpl.
+ intros [f fε]; simpl in *.
  specialize (fε (fun α => (inj (nth α)))); cbn in *.
  admit.
+ simpl.
intros.
apply fan_spec.
Abort.

