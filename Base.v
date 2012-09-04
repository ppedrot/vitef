Require Setoid.
Require Import Morphisms.

(* Sets, a la Aczel *)
Inductive V : Type := V_const : forall {X : Type}, (X -> V) -> V.

(* Set membership *)
Inductive V_rel : V -> V -> Prop :=
 V_rel_def : forall {X : Type} (f : X -> V) (x : X), V_rel (f x) (V_const f).

Notation "x 'ε' y" := (V_rel x y) (at level 70).

Lemma V_rel_inv : forall X (f : X -> V) (P : V -> Prop),
  (forall x, P (f x)) -> forall y, V_rel y (V_const f) -> P y.
Proof.
 intros X f P H y H0.
 (* "inversion H0" can't quite handle the dependent types, so we
    roll our own inversion. *)
 revert H.
 refine (match H0 in (V_rel a b) return
           (match b return Prop with
            | V_const X' f' => (forall x:X', P (f' x)) -> P a
            end) with
         | V_rel_def X' f' _ => _
         end). trivial.
Qed.

Lemma wf_V_rel : well_founded V_rel.
Proof.
intros x; induction x as [X Xf].
constructor; intros [Y Yf]; apply V_rel_inv; assumption.
Qed.

CoInductive V_eq (x : V) (y : V) : Prop := {
  V_eq_l : forall xs, V_rel xs x -> exists ys, V_rel ys y /\ V_eq xs ys;
  V_eq_r : forall ys, V_rel ys y -> exists xs, V_rel xs x /\ V_eq xs ys
}.

Notation "x ≅ y" := (V_eq x y) (at level 70).

Instance V_eq_refl : Reflexive V_eq.
Proof.
cofix; intros [X Xf]; constructor; intros xs Hxs; exists xs; auto.
Qed.

Instance V_eq_sym : Symmetric V_eq.
Proof.
cofix; intros [X Xf] [Y Yf] [Hl Hr]; split.
  intros ys Hys; destruct (Hr ys Hys) as [xs Hxs]; exists xs; intuition.
  intros ys Hys; destruct (Hl ys Hys) as [xs Hxs]; exists xs; intuition.
Qed.

Instance V_eq_trans : Transitive V_eq.
Proof.
cofix IH; intros [X Xf] [Y Yf] [Z Zf] [H1l H1r] [H2l H2r]; split.
  { intros xs Hxs.
    destruct (H1l xs Hxs) as [ys [Hys Heql]].
    destruct (H2l ys Hys) as [zs [Hzs Heqr]].
    exists zs; split; [assumption|eapply IH; eassumption].
  }
  { intros xs Hxs.
    destruct (H2r xs Hxs) as [ys [Hys Heql]].
    destruct (H1r ys Hys) as [zs [Hzs Heqr]].
    exists zs; split; [assumption|eapply IH; eassumption].
  }
Qed.

Record mem (x y : V) : Prop := {
  mem_set : V;
  mem_set_eq : mem_set ≅ x;
  mem_spec : V_rel mem_set y
}.

Notation "x ∈ y" := (mem x y) (at level 70).

Instance Proper_mem : Proper (V_eq ==> V_eq ==> iff) mem.
Proof.
apply proper_sym_impl_iff_2; try apply V_eq_sym.
intros x1 x2 Hx y1 y2 Hy [x3 Heq Hr].
destruct Hy as [Hyl Hyr]; specialize (Hyl _ Hr).
destruct Hyl as [x4 [Hi4 Hx4]].
exists x4; [|assumption].
symmetry; transitivity x3; [|assumption].
symmetry; transitivity x1; assumption.
Qed.

Lemma subrelation_mem_rel : subrelation V_rel mem.
Proof.
intros x y H; exists x; [reflexivity|assumption].
Qed.

Lemma wf_mem : well_founded mem.
Proof.
intros x; constructor; intros y H.
destruct H as [z Heq H]; apply (wf_V_rel) in H; clear x.
revert y Heq; induction H as [x H IH]; intros y Hy.
constructor; intros z [s Heq Hs].
destruct Hy as [_ Hy]; specialize (Hy _ Hs); destruct Hy as [u [? Hu]].
apply (IH u); [assumption|].
transitivity s; assumption.
Qed.

Definition included x y := forall e, e ε x -> e ∈ y.

Notation "x ⊆ y" := (included x y) (at level 70).

Definition extensional (f : V -> V) := Proper (V_eq ==> V_eq) f.

Lemma extensionality : forall x y, x ⊆ y -> y ⊆ x -> x ≅ y.
Proof.
cofix IH; intros x y Hl Hr; split.
  + intros xs Hx; specialize (Hl _ Hx); destruct Hl as [x' Heq Hin]; exists x'.
    split; [assumption|symmetry; assumption].
  + intros ys Hy; specialize (Hr _ Hy); destruct Hr as [y' Heq Hin]; exists y'.
    split; assumption.
Qed.

Lemma mem_included_compat : forall x y z, x ∈ y -> y ⊆ z -> x ∈ z.
Proof.
intros x y z [x' Heq H] Hi.
specialize (Hi _ H).
rewrite <- Heq; assumption.
Qed.

Lemma included_spec : forall x y, (x ⊆ y) <-> (forall z, z ∈ x -> z ∈ y).
Proof.
intros x y; split; intros H.
+ intros z Hz; eapply mem_included_compat; eassumption.
+ intros z Hz; apply subrelation_mem_rel in Hz; intuition.
Qed.

Instance Proper_included : Proper (V_eq ==> V_eq ==> iff) included.
Proof.
apply proper_sym_impl_iff_2; try apply V_eq_sym.
intros x1 x2 Hx y1 y2 Hy Hs z Hz.
rewrite <- Hy; eapply mem_included_compat; [|eassumption].
rewrite Hx; apply subrelation_mem_rel; assumption.
Qed.

Instance Transitive_included : Transitive included.
Proof.
intros x y z Hl Hr.
apply included_spec; intros a Ha.
apply (mem_included_compat _ y); [|assumption].
eapply (mem_included_compat); eassumption.
Qed.

Definition empty : V := V_const (fun f => False_rect _ f).
Definition singleton (x : V) := V_const (fun u => unit_rect _ x u).

Definition comprehension (x : V) (P : V -> Prop) : V.
Proof.
destruct x as [X Xf].
exists {x : X | P (Xf x)}.
intros [x _]; apply (Xf x).
Defined.

Definition powerset (x : V) : V.
Proof.
destruct x as [X Xf].
exists (X -> Prop); intros f.
exists {x : X | f x}.
exact (fun e => Xf (proj1_sig e)).
Defined.

Definition collection (x : V) (f : V -> V) : V.
Proof.
destruct x as [X Xf].
exists X; intros x; apply (f (Xf x)).
Defined.

Definition cup (x y : V) : V :=
  let (X, Xf) := x in
  let (Y, Yf) := y in
  @V_const (X + Y) (fun s => match s with inl x => Xf x | inr y => Yf y end).

Definition union (x : V) : V.
Proof.
destruct x as [X Xf].
exists {x : _ & match Xf x with V_const Y _ => Y end}.
intros [x y].
destruct (Xf x) as [Y Yf].
exact (Yf y).
Defined.

Definition pair (x y : V) : V :=
  @V_const bool (fun b => if b then x else y).

Lemma empty_spec : forall x : V, ~ x ∈ empty.
Proof.
intros x [z Heq H].
inversion H using V_rel_inv; tauto.
Qed.

Lemma singleton_spec : forall x y, x ∈ singleton y <-> x ≅ y.
Proof.
intros x y; split; intros H.
  + destruct H as [z Heq H].
    revert Heq; inversion H using V_rel_inv; intros []; simpl; symmetry; assumption.
  + exists y; [symmetry; assumption|].
    change y with (unit_rect (fun _ => V) y tt) at 1; now constructor.
Qed.

Lemma comprehension_spec : forall x y P, Proper (V_eq ==> iff) P ->
    y ∈ comprehension x P <-> (y ∈ x /\ P y).
Proof.
intros x y P HP; split; intros H.
  + destruct H as [z Heq H]; rewrite <- Heq; clear y Heq.
    destruct x as [X Xf]; inversion H using V_rel_inv; clear z H.
    intros [x Hx]; split; [apply subrelation_mem_rel; constructor|assumption].
  + destruct H as [[z Heq H] Hr]; exists z; [assumption|].
    assert (Hz : P z) by (rewrite Heq; assumption); clear y Heq Hr.
    destruct x as [X Xf]; revert Hz; inversion H using V_rel_inv; clear z H; intros z Hz.
    pose (p := exist (fun z => P (Xf z)) z Hz).
    change (Xf z) with ((fun p : {_ | _} => let (x, _) := p in Xf x) p).
    now constructor.
Qed.

Lemma collection_spec : forall x y f, extensional f ->
  y ∈ collection x f <-> (exists z, z ∈ x /\ y ≅ f z).
Proof.
intros x y f Hf; split.
  + intros [z Heq H]; revert Heq; destruct x as [X Xf].
    inversion H using V_rel_inv; clear z H; intros z H.
    exists (Xf z); split.
    - apply subrelation_mem_rel; constructor.
    - symmetry; assumption.
  + intros [z [[z' Heq' H] Heq]]; exists (f z').
    - rewrite Heq; apply Hf; assumption.
    - destruct x as [X Xf]; inversion H using V_rel_inv.
      clear; intros x; change (f (Xf x)) with ((fun x => f (Xf x)) x).
      now constructor.
Qed.

Lemma powerset_spec : forall x y, x ∈ powerset y <-> x ⊆ y.
Proof.
intros x y; split.
  + intros [z Heq H]; revert Heq; destruct y as [Y Yf].
    inversion H using V_rel_inv; clear z H; intros f Heq z Hz.
    destruct Heq as [_ Heq]; specialize (Heq _ Hz); destruct Heq as [zs [Hzl Hzr]].
    exists zs; [assumption|].
    clear - Hzl; inversion Hzl using V_rel_inv; clear.
    intros [x Hx]; simpl; constructor.
  + intros Hsub; destruct y as [Y Yf].
    pose (z := @V_const {y : Y | Yf y ∈ x} (fun y => Yf (proj1_sig y))); exists z.
    - apply extensionality.
      { intros s Hs; inversion Hs using V_rel_inv; clear s Hs; intros [? ?]; assumption. }
      {
        assert (Hrw : z ≅ x). {
          apply extensionality.
          + intros y Hy; inversion Hy using V_rel_inv; clear; intros [? ?]; assumption.
          + intros y Hy; specialize (Hsub _ Hy); destruct Hsub as [s Heq H].
            revert Hy Heq; inversion H using V_rel_inv; clear s H; intros s H Heq.
            exists (Yf s); [assumption|].
            assert (Hin : Yf s ∈ x) by (rewrite Heq; apply subrelation_mem_rel; assumption).
            pose (p := exist (fun y => Yf y ∈ x) s Hin).
            change (Yf s) with ((fun p => Yf (proj1_sig p)) p); constructor.
        }
        intros s Hs; rewrite Hrw; apply subrelation_mem_rel; assumption.
      }
    - change z with ((fun P => @V_const {y : Y | P y} (fun y => Yf (proj1_sig y))) (fun y => Yf y ∈ x)).
      now constructor.
Qed.

Lemma cup_spec : forall x y z, z ∈ cup x y <-> z ∈ x \/ z ∈ y.
Proof.
intros x y z; destruct x as [X Xf]; destruct y as [Y Yf]; split.
  + intros [s Heq H]; rewrite <- Heq; clear Heq.
    inversion H using V_rel_inv.
    intros [x|y]; [left|right]; apply subrelation_mem_rel; constructor.
  + intros [[s Heq H]|[s Heq H]].
    - exists s; [assumption|].
      inversion H using V_rel_inv; clear; intros s.
      unfold cup; match goal with [ |- _ ε V_const ?f ] => set (F := f) end.
      change (Xf s) with (F (inl s)); constructor.
    - exists s; [assumption|].
      inversion H using V_rel_inv; clear; intros s.
      unfold cup; match goal with [ |- _ ε V_const ?f ] => set (F := f) end.
      change (Yf s) with (F (inr s)); constructor.
Qed.

Lemma union_spec : forall x y, x ∈ union y <-> exists z, x ∈ z /\ z ∈ y.
Proof.
intros x y; split.
  + intros [z Heq H]; destruct y as [Y Yf].
    revert Heq; inversion H using V_rel_inv; clear z H.
    intros [y z]; remember (Yf y) as s; destruct s as [Z Zf]; simpl.
    intros Hrw; exists (V_const Zf); split.
    - exists (Zf z); [assumption|constructor].
    - exists (Yf y); [match goal with [ H : _ = Yf y |- _ ] => rewrite H end; reflexivity|constructor].
  + intros [z [Hzl Hzr]]; destruct Hzl as [l Heql Hl]; destruct Hzr as [r Heqr Hr].
    rewrite <- Heql; clear x Heql.
    destruct z as [Z Zf]; destruct y as [Y Yf].
    inversion Hl using V_rel_inv; clear l Hl; intros l.
    revert Heqr; inversion Hr using V_rel_inv; clear r Hr; intros r Heqr.
    destruct Heqr as [_ Heqr]; specialize (Heqr _ (V_rel_def Zf l)).
    destruct Heqr as [z [Hzl Hzr]]; exists z; [assumption|].
    clear Z Zf l Hzr; unfold union; match goal with [ |- ?t ε V_const ?f ] => set (F := f) end.
    assert (Hf : exists p, z = F p). {
      remember (Yf r) as m; destruct m as [M Mf].
      inversion Hzl using V_rel_inv; clear z Hzl; intros z.
      pose (cz := match Heqm in _ = u return match u with V_const Z _ => Z end with eq_refl => z end).
      pose (p := existT (fun y => match Yf y with V_const Z _ => Z end) r cz).
      exists p; simpl; clear; destruct Heqm; reflexivity.
    }
    destruct Hf as [p Hrw]; rewrite Hrw; constructor.
Qed.

Lemma pair_spec : forall x y z, z ∈ pair x y <-> z ≅ x \/ z ≅ y.
Proof.
intros [X Xf] [Y Yf] z; split.
  + intros [m Heq H]; rewrite <- Heq; clear z Heq.
    inversion H using V_rel_inv; clear m H; intros [|].
    - left; reflexivity.
    - right; reflexivity.
  + intros [H|H]; rewrite H; apply subrelation_mem_rel.
    - change (V_const Xf) with ((fun b : bool => (if b then V_const Xf else V_const Yf)) true); constructor.
    - change (V_const Yf) with ((fun b : bool => (if b then V_const Xf else V_const Yf)) false); constructor.
Qed.

Instance Proper_singleton : Proper (V_eq ==> V_eq) singleton.
Proof.
intros x1 x2 Hx; apply extensionality; intros z Hz; apply subrelation_mem_rel in Hz.
+ apply singleton_spec; apply singleton_spec in Hz; rewrite Hx in *; assumption.
+ apply singleton_spec; apply singleton_spec in Hz; rewrite Hx in *; assumption.
Qed.

Instance Proper_pair : Proper (V_eq ==> V_eq ==> V_eq) pair.
Proof.
intros x1 x2 Hx y1 y2 Hy; apply extensionality; intros z Hz; apply subrelation_mem_rel in Hz.
+ apply pair_spec; apply pair_spec in Hz; rewrite Hx, Hy in *; tauto.
+ apply pair_spec; apply pair_spec in Hz; rewrite Hx, Hy in *; tauto.
Qed.

Instance Proper_comprehension :
  Proper (V_eq ==> respectful V_eq iff ==> V_eq) comprehension.
Proof.
intros x1 x2 Hx P1 P2 HP.
assert (HP1 : Proper (V_eq ==> iff) P1).
{ clear - HP; intros x1 x2 Hx; rewrite (HP x1 x2 Hx); symmetry; apply HP; reflexivity. }
assert (HP2 : Proper (V_eq ==> iff) P2).
{ clear - HP; intros x1 x2 Hx; symmetry; rewrite <- (HP x1 x2 Hx); apply HP; reflexivity. }
apply extensionality; apply included_spec; intros z Hz.
+ apply comprehension_spec; [assumption|]; apply comprehension_spec in Hz; [|assumption].
  destruct Hz as [Hzl Hzr]; rewrite <- Hx; split; [assumption|].
  apply (HP z z); [reflexivity|assumption].
+ apply comprehension_spec; [assumption|]; apply comprehension_spec in Hz; [|assumption].
  destruct Hz as [Hzl Hzr]; rewrite Hx; split; [assumption|].
  apply <- (HP z z); [assumption|reflexivity].
Qed.

Instance Proper_collection :
  Proper (V_eq ==> respectful V_eq V_eq ==> V_eq) collection.
Proof.
intros x1 x2 Hx f1 f2 Hf.
assert (Hf1 : extensional f1).
{ clear - Hf; intros x1 x2 Hx; rewrite (Hf x1 x2 Hx); symmetry; apply Hf; reflexivity. }
assert (Hf2 : extensional f2).
{ clear - Hf; intros x1 x2 Hx; symmetry; rewrite <- (Hf x1 x2 Hx); apply Hf; reflexivity. }
apply extensionality; apply included_spec; intros z Hz.
+ apply collection_spec; [assumption|]; apply collection_spec in Hz; [|assumption].
  destruct Hz as [r [Hr Hz]]; exists r; rewrite <- Hx; split; [assumption|].
  rewrite Hz; apply Hf; reflexivity.
+ apply collection_spec; [assumption|]; apply collection_spec in Hz; [|assumption].
  destruct Hz as [r [Hr Hz]]; exists r; rewrite Hx; split; [assumption|].
  rewrite Hz; symmetry; apply Hf; reflexivity.
Qed.

Instance Proper_union : Proper (V_eq ==> V_eq) union.
Proof.
intros x1 x2 Hx.
apply extensionality; apply included_spec; intros z Hz; apply union_spec in Hz;
destruct Hz as [r [Hz Hr]]; apply union_spec; exists r; split;
solve [assumption|rewrite <- Hx; assumption|rewrite Hx; assumption].
Qed.

Instance Proper_powerset : Proper (V_eq ==> V_eq) powerset.
Proof.
intros x1 x2 Hx.
apply extensionality; apply included_spec; intros z Hz; apply powerset_spec in Hz;
apply powerset_spec; first [rewrite Hx|rewrite <- Hx]; assumption.
Qed.
