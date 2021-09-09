Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Set Cumulative .
Set Universe Polymorphism.

Inductive path@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := refl : path x x.
Arguments refl {_ _}.

Definition path_sym {A x y} (e : @path A x y) : path y x :=
match e in path _ z return path z x with refl => refl end.

Definition path_trs {A x y z} (e : @path A x y) (e' : @path A y z) : path x z :=
match e' in path _ w return path x w with refl => e end.

Lemma path_inv : forall {A x y} (e : @path A x y), path (path_trs e (path_sym e)) refl .
Proof.
destruct e; reflexivity.
Defined.

Lemma sym_trs : forall {A x y z} (e : @path A x y) (e' : @path A y z),
  path (path_sym (path_trs e e')) (path_trs (path_sym e') (path_sym e)).
Proof.
destruct e, e'.
reflexivity.
Defined.

Lemma sym_sym : forall {A x y} (e : @path A x y), path (path_sym (path_sym e)) e.
Proof.
intros; destruct e.
reflexivity.
Defined.

Definition apf {A} {B : A -> Type} {f g : forall x, B x}
  (e : path f g) (x : A) : path (f x) (g x) :=
match e in path _ h return path (f x) (h x) with refl => refl end.

Definition ap {A B} {x y : A} (f : A -> B) (e : path x y) : path (f x) (f y) :=
match e in path _ z with refl => refl end.

Lemma isContr_K : forall {A : Type} (x : A) (hx : forall y, path x y) {y} (p q : path x y), path p q.
Proof.
intros A x hx y p q.
pose (φ u v := path_trs (path_sym (hx u)) (hx v)).
assert (e' : forall u v (p : path u v), path (φ u v) p).
{ intros u v []; compute; destruct hx; reflexivity. }
unshelve refine (path_trs _ (e' _ _ _)).
refine (path_sym (e' _ _ _)).
Defined.

Definition rew {A : Type} {x y : A} (e : path x y) (B : A -> Type) (p : B x) : B y.
Proof.
destruct e; exact p.
Defined.

Definition rew_trs {A} {x y z : A} (e : path x y) (e' : path y z) (B : A -> Type) (p : B x) :
  path (rew (path_trs e e') B p) (rew e' B (rew e B p)).
Proof.
destruct e'; reflexivity.
Defined.

Definition rew_ap {A B} {x y : A} (f : A -> B) (e : path x y) C p :
  path (rew (ap f e) C p) (rew e (fun z => C (f z)) p).
Proof.
destruct e; reflexivity.
Defined.

(*
Lemma ap_rew {A B} {x y : A} (f : A -> B) (e : path x y) l r (p : path (l x) (r x)) :
  path
    (ap f (rew e (fun z : A => path (l z) (r z)) p))
    (rew e (fun x : A => path (f (l x)) (f (r x))) (ap f p)).
Proof.
destruct e; reflexivity.
Defined.
*)

Definition rew_app {A B C} {x y : A} (f : forall (x : A), B x -> C x) (e : path x y) p :
  path (rew e C (f x p)) (f y (rew e B p)).
Proof.
destruct e.
reflexivity.
Defined.

(*
Definition rew_path_l {A B} (f : forall x : A, B x) {x y : A} (e : path x y)
  (p : path z (f x)) :
  path (rew e (fun z => path (f z) (g z)) p) (path_trs _ _).
*)

Lemma sym_ap : forall {A B} {x y : A} (f : A -> B) (e : path x y),
  path (path_sym (ap f e)) (ap f (path_sym e)).
Proof.
destruct e; reflexivity.
Defined.

Record sig (A : Type) (B : A -> Type) := pair { fst : A; snd : B fst }.

Arguments fst {_ _}.
Arguments snd {_ _}.

Lemma sig_path : forall {A B} {p q : sig A B}
  (efst : path p.(fst) q.(fst)) (esnd : path (rew efst B p.(snd)) q.(snd)),
  path p q.
Proof.
intros A B [pf ps] [qf qs] ef es; simpl in *.
destruct ef, es.
reflexivity.
Defined.

Definition isContr (A : Type) := sig A (fun x => forall y, path x y).

Definition isEquiv {A B} (f : A -> B) :=
  forall y : B, isContr (sig A (fun x => path y (f x))).
(*
  g : B -> A;
  ge : forall y : B, path y (f (g y))
  { fe : forall (y : B) (x : A) (e : path y (f x)), path (x, e) (g y, ge y) }
  fe : forall (x : A), path x (g (f x))
  fg : forall (x : A), hpath (fe x) refl (ge (f x))
*)
 
Record isEquiv' {A B} (f : A -> B) := {
  eqv_rev : B -> A;
  eqv_eql : forall (y : B), path y (f (eqv_rev y));
  eqv_eqr : forall (x : A), path x (eqv_rev (f x));
(*   eqv_sqs : forall (x : A), hpath (eqv_eqr x) (fun y => path (f x) (f y)) refl (eqv_eql (f x));  *)
  eqv_sqs : forall (x : A), path (ap f (eqv_eqr x)) (eqv_eql (f x)); 
}.

Record isIso {A B} (f : A -> B) := {
  iso_rev : B -> A;
  iso_eql : forall (y : B), path y (f (iso_rev y));
  iso_eqr : forall (x : A), path x (iso_rev (f x));
}.

Lemma isIso_isEquiv : forall A B (f : A -> B), isIso f -> isEquiv f.
Proof.
intros A B f [g φ ψ].
intros y; unshelve econstructor.
+ exists (g (f (g y))).
  refine (path_trs (φ y) (ap f (ψ (g y)))).
Show Proof.
+ intros [z p].
  unshelve refine (sig_path _ _).
  - simpl.
    refine (path_trs _ (path_sym (ψ z))).
    refine (path_trs _ (ap g p)).
    refine (path_sym (ap g (φ y))).
  - simpl.
    rewrite <- (sym_sym p).
    set (q := path_sym p); clearbody q; clear p.
    destruct q; simpl.
    rewrite <- sym_trs.
    rewrite (rew_app (fun x => path_trs (φ (f z)))).
    match goal with [ |- path (path_trs ?p ?q) refl ] =>
      assert (e : path q (path_sym p))
    end.
    2:{ rewrite e; apply path_inv. }
    rewrite sym_trs, sym_ap.
    set (q := path_sym (φ (f z))); clearbody q.
    rewrite rew_trs.
    rewrite rew_ap.
    rewrite (rew_app (fun y => ap f)).
    rewrite (rew_app (fun x => ap f)).

    set (p := 
    (rew q (fun y : B => path (g (f z)) (g y))
               (ψ (g (f z))))).
    simpl in p.
    pose (r := path_trs ((ψ _)) (ap g q)).
    assert (e : p = r).
    { unfold p, r.
    destruct q; reflexivity. }
    rewrite e; unfold p, r; clear e p r.
Abort.

Definition isEquiv_id {A} : isEquiv (fun x : A => x).
Proof.
intros x.
unshelve econstructor.
+ exists x; reflexivity.
+ intros [y e].
  destruct e; reflexivity.
Defined.

Definition Equiv A B := sig (A -> B) isEquiv.

Definition Equiv_path {A B} (e : path A B) : Equiv A B.
Proof.
destruct e; exists (fun x => x); apply isEquiv_id.
Defined.

Axiom Univalence : forall A B, isEquiv (@Equiv_path A B).

Axiom Funext : forall A B f g, isEquiv (@apf A B f g).

Lemma funext : forall {A : Type} {B : A -> Type} {f g : forall x : A, B x},
  (forall x, path (f x) (g x)) -> path f g.
Proof.
intros A B f g e.
refine (Funext A B f g e).(fst).(fst).
Defined.

Definition apf_funext {A B f g} e :
  path (@funext A B f g (apf e)) e.
Proof.
unfold funext.
destruct Funext as [F HF]; simpl.
refine (ap fst (HF (pair _ _ _ _))).
reflexivity.
Defined.

Lemma isContr_fiber : forall A B (f : A -> B) (x : A),
  isContr (sig B (fun y => path (f x) y)).
Proof.
intros A B f x.
unshelve econstructor.
+ exists (f x).
  reflexivity.
+ intros [x' hx].
  destruct hx.
  reflexivity.
Defined.

Lemma ap_cmp : forall {A B C} {x y : A} (f : A -> B) (g : B -> C) (e : path x y),
  path (ap g (ap f e)) (ap (fun x => g (f x)) e).
Proof.
intros A B C x y f g []; reflexivity.
Defined.

Lemma ap_refl : forall {A B} {x : A} (f : A -> B), path (@ap A B x x f refl) refl.
Proof.
reflexivity.
Defined.

Lemma isEquiv_Equiv' : forall A B (f : A -> B), Equiv (isEquiv f) (isEquiv' f).
Proof.
intros A B f.
unshelve econstructor.
+ intros Hf.
  unshelve econstructor.
  - refine (fun y => fst (fst (Hf y))).
  - intros y; simpl.
    refine (Hf y).(fst).(snd).
  - intros x; simpl.
    destruct (Hf (f x)) as [[x' hx'] he]; clear Hf; simpl in *.
    refine (ap fst (path_sym (he (pair _ _ x refl)))).
  - intros x; simpl.
    destruct (Hf (f x)) as [[x' hx'] he]; clear Hf; simpl in *.
    set (p := pair _ (fun y => path (f x) (f y)) x refl) in *.
    set (q := pair _ (fun y => path (f x) (f y)) x' hx') in *.
    change hx' with (snd q).
    refine (path_trs (ap_cmp fst f (path_sym (he p))) _).
    clearbody q; clear x' hx'.
(*     refine (rew _ _ (he _)). *)
    assert (e : path p q).
    { apply path_sym, he. }
    revert he.
    destruct e; intros he.
    refine (path_trs (path_sym (ap_cmp fst f _)) _).
    simpl.
    refine (path_trs _ (ap_refl _)).
    refine (ap _ _).
    refine (path_trs _ (ap_refl _)).
    refine (ap _ _).
    refine (isContr_K _ he _ _).
+ intros [g φ ψ ε].
  unshelve econstructor; [unshelve econstructor|].
  - intros y.
    unshelve refine (pair _ _ (pair _ _ (g y) (φ y)) _).
    intros [x e].
    admit.
Admitted.

Definition isProp@{i} (A : Type@{i}) := forall x y : A, path x y.

Definition hProp@{i j} : Type@{j} := sig@{j i} Type@{i} isProp.
Definition hElt@{i j} (A : hProp@{i j}) : Type@{i} := fst A.

Coercion hElt : hProp >-> Sortclass.

Lemma isProp_isContr : forall A, isProp (isContr A).
Proof.
intros A [x hx] [y hy].
destruct (hx y).
assert (e : path hx hy).
{ apply funext; intros y.
  apply isContr_K, hx.
}
destruct e; reflexivity.
Qed.

Lemma isProp_forall : forall A (B : A -> Type),
  (forall x : A, isProp (B x)) -> isProp (forall x : A, B x).
Proof.
intros A B hB f g.
apply funext; intros x.
refine (hB x _ _).
Defined.

Lemma isProp_isEquiv : forall A B (f : A -> B), isProp (isEquiv f).
Proof.
intros A B f.
apply isProp_forall; intros y.
apply isProp_isContr.
Defined.


Lemma isProp_isEquiv' : forall A B (f : A -> B), isProp (isEquiv' f).
Proof.
intros A B f [g φ ψ ε] [h ζ κ η].
assert (e : path g h).
{ refine (funext (fun y => _)).
  refine (path_trs (κ _) (ap h (path_sym (φ _)))).
}
revert ζ κ η.
pattern h.
refine (rew e _ _); clear e h.
intros ζ κ η.
assert (e : path φ ζ).
{
  apply funext; intros y.
  assert (e : path (f (g y)) y).
  { apply (path_sym (φ y)). }
  refine (rew e (fun z => path (φ z) (ζ z)) _); clear e.
  rewrite <- ε, <- η.
  apply ap.
  

  assert (e : path (g (f (g y))) (g y)).
  { apply (path_sym (κ (g y))). }
  refine (rew e (fun z => path (ψ z) (κ z)) _); clear e.
Abort.

Monomorphic Universe u.

Axiom I : Set.
Axiom O : I -> hProp@{Set u}.

Module Sh.

Private Inductive Shf@{i} (A : Type@{i}) : Type@{i} :=
| ret : A -> Shf A
| ask : forall (i : I) (k : O i -> Shf A), Shf A.

Arguments ret {_}.
Arguments ask {_}.

Axiom eqn@{i} : forall {A : Type@{i}} (i : I) (s : Shf@{i} A),
  path (ask i (fun _ => s)) s.

Fixpoint Shf_rect@{i j} (A : Type@{i})
  (P : Shf@{i} A -> Type@{j})
  (pret : forall (a : A), P (ret a))
  (pask : forall (i : I) (k : O i -> Shf A), (forall o, P (k o)) -> P (ask i k))
  (peqn : forall (s : Shf A) (ps : P s) (i : I),
    path (rew (eqn i s) P (pask i (fun _ => s) (fun _ => ps))) ps)
  s {struct s} : P s.
Proof.
refine (
match s with
| ret x => pret x
| ask i k => pask i k (fun o => Shf_rect A P pret pask peqn (k o))
end
).
Defined.

End Sh.

Import Sh.

Definition isSheafE@{i} (A : Type@{i}) : Type@{i} :=
  forall (i : I), @isEquiv A (O i -> A) (fun x _ => x).

Definition invSh {A : Type} (i : I)
  (hA : (O i -> A) -> A) (εA : forall x : A, path (hA (fun _ => x)) x)
  (k : O i -> A) : path (fun _ => hA k) k.
Proof.
refine (funext (fun o => _)).
refine (path_trs _ (εA _)).
refine (ap hA (funext (fun o' => ap k (snd (O i) o' o)))).
Defined.

Record isSheaf@{i} (A : Type@{i}) : Type@{i} := {
  shf_fun : forall (i : I) (k : O i -> A), A;
  shf_spc : forall (i : I) (x : A), path (shf_fun i (fun _ => x)) x;
}.

Lemma isSheaf_unq : forall (A : Type) i (hA : (O i -> A) -> A) εA (x : A),
  path (ap (fun x _ => x) (εA x)) (invSh i hA εA (fun _ => x)).
Proof.
intros A i hA εA x.
unfold invSh.
rewrite <- (apf_funext (ap _ (εA x))).
refine (ap _ _).
apply funext; intros o.
destruct (εA x); simpl.
clear εA.
change refl with (@ap (O i -> A) A (fun _ : O i => x) _ hA refl) at 1.
apply ap.
rewrite <- (apf_funext refl).
apply ap.
apply funext; intros o'.
unfold apf, ap.
destruct (snd (O i)).
reflexivity.
Defined.

Lemma apf_inv : forall {A : Type} {B : A -> Type} {f g : forall x : A, B x}
  (p q : path f g), (forall x : A, path (apf p x) (apf q x)) -> path p q.
Proof.
intros A B f g p q φ.
refine (path_trs _ (apf_funext q)).
refine (path_trs (path_sym (apf_funext p)) _).
refine (ap _ _).
refine (funext φ).
Defined.

Arguments shf_fun {_}.
Arguments shf_spc {_}.

Lemma isSheaf_isEquiv_ret : forall (A : Type) (i : I), isSheaf A ->
  @isEquiv A (O i -> A) (fun x _ => x).
Proof.
intros A i [f fs] k.
unshelve econstructor.
+ exists (f i k).
  refine (path_sym (invSh _ _ (fun x => fs i x) k)).
+ intros [x e]; simpl.
  unshelve refine (sig_path _ _); simpl.
  - refine (path_trs _ (fs i x)).
    refine (ap (f i) e).
  - apply apf_inv; intros o.
    refine (ap (fun p => apf p o) _).
    change (fun x => fs i x) with (fs i).
    rewrite rew_trs, !rew_ap.
    assert (p : path
      ((rew e (fun z : O i -> A => path k (fun _ : O i => f i z))
        (path_sym (invSh i (f i) (fs i) k))))
      (path_trs e (path_sym (invSh i (f i) (fs i) _)))
    ).
    { destruct e; simpl; destruct invSh; reflexivity. }
    rewrite p; clear p.
    rewrite <- isSheaf_unq.
    rewrite (rew_app (fun z p => path_trs e (path_sym (ap (fun (x0 : A) (_ : O i) => x0) p))) (fs i x)).
    refine (@path_trs _ _ (path_trs e refl) _ _ _); [|destruct e; reflexivity].
    refine (ap (path_trs e) _).
    destruct (fs i x); reflexivity.
Defined.

Definition Sheaf@{i j} : Type@{j} := sig@{j j} Type@{i} isSheaf.

Definition U := Shf Sheaf.

Definition Prod (A : Type) (B : A -> Sheaf) : Sheaf.
Proof.
unshelve econstructor.
+ exact (forall x : A, fst (B x)).
+ unshelve econstructor.
  - intros i k x; refine ((B x).(snd).(shf_fun) i (fun o => k o x)).
  - intros f i; simpl.
    apply funext; intros x.
    apply shf_spc.
Defined.

Definition WUniv : forall A B, Equiv A B -> path A B.
Proof.
intros A B f.
refine (Univalence A B f).(fst).(fst).
Defined.

Definition rew_funext {A B f g} e {X} (i : X -> A) (C : forall (x : X), B (i x) -> Type) p :
  path
    (rew (@funext A B f g e) (fun h => forall x : X, (C x (h (i x)))) p)
    (fun x => rew (e (i x)) (C x) (p x)).
Proof.
apply funext; intros x.
unfold funext.
destruct Funext as [[q hq] φ]; simpl.
destruct q; simpl in *.
clear φ.
destruct (path_sym hq); simpl.
reflexivity.
Defined.

Lemma isProp_isSheaf : forall (A : Type), isProp (isSheaf A).
Proof.
intros A [f fs] [g gs].
cut (sig (path f g) (fun e => path (rew e (fun h => forall (i : I) (x : A), path (h i (fun _ : O i => x)) x) fs) gs)). 
{ intros [p q]; destruct p, q; reflexivity. }
unshelve econstructor.
+ apply funext; intros i.
  apply funext; intros k.
  pose (p := invSh i (f i) (fs i) k).
  refine (path_trs _ (ap (g i) p)).
  refine ((path_sym (gs i _))).
+ simpl.
  apply funext; intros i.
  apply funext; intros x.
  match goal with [ |- path (rew (funext ?e) _ _ _ _) _ ] =>
    rewrite (rew_funext e (fun x => x) (fun i h => forall (x : A), path (h _) x))
  end.
  match goal with [ |- path (rew (funext ?e) _ _ _) _ ] =>
    rewrite (rew_funext e (fun x => fun _ => x) (fun x h => path h x))
  end.
  rewrite <- isSheaf_unq; simpl.
  destruct (fs i x); simpl.
  destruct gs; reflexivity.
Defined.

Definition El : U -> Sheaf.
Proof.
simple refine (Shf_rect Sheaf _ (fun A => A) (fun i k A => Prod (O i) A) _); simpl.
+ intros A₀ [A hA] i; simpl.
  simple refine (sig_path _ _); simpl.
  - apply path_sym. apply WUniv.
    destruct (eqn i A₀); simpl.
    exists (fun x _ => x).
    apply isSheaf_isEquiv_ret, hA.
  - destruct (eqn i A₀); simpl.
    refine (isProp_isSheaf _ _ _).
Defined.
