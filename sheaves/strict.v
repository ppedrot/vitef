Set Primitive Projections.

Axiom I : Set.
Axiom O : I -> SProp.
Definition ℙ := forall i : I, O i.

Inductive seq {A : Type} (x : A) : A -> SProp := srefl : @seq A x x.

Axiom uip : forall A (x y : A), seq x y -> x = y.
Axiom uip₀ : forall A (x y : A) (p q : x = y), p = q.

Axiom sfunext : forall (A : SProp) (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom funext : forall A (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom pi : forall (A : Prop) (p q : A), p = q.

Record isSheaf (A : Type) := {
  shf_elt : forall i : I, (O i -> A) -> A;
  shf_spc : forall i (x : A), x = shf_elt i (fun _ => x);
}.

Arguments shf_elt {_}.
Arguments shf_spc {_}.

Module Import Sh.

Private Inductive Shf (A : Type) :=
| ret : A -> Shf A
| ask : forall i, (O i -> Shf A) -> Shf A.

Arguments ret {_}.
Arguments ask {_}.

Axiom eqn : forall {A} (i : I) (x : Shf A), ask i (fun _ => x) = x.

Fixpoint Shf_rect (A : Type) (P : Shf A -> Type)
  (ur : forall (x : A), P (ret x))
  (ua : forall (i : I) (k : O i -> Shf A),
    (forall o : O i, P (k o)) -> P (ask i k))
  (ue : forall (i : I) (x : Shf A) (px : P x),
    match eqn i x in _ = e return P e with eq_refl => ua i (fun _ => x) (fun _ => px) end = px)
  (x : Shf A) {struct x} :
  P x :=
match x with
| ret x => ur x
| ask i k => ua i k (fun o => Shf_rect A P ur ua ue (k o))
end.

Fixpoint Shf_sind (A : Type) (P : Shf A -> SProp)
  (ur : forall (x : A), P (ret x))
  (ua : forall (i : I) (k : O i -> Shf A),
    (forall o : O i, P (k o)) -> P (ask i k))
  (x : Shf A) {struct x} :
  P x :=
match x with
| ret x => ur x
| ask i k => ua i k (fun o => Shf_sind A P ur ua (k o))
end.

End Sh.

Inductive Shε {A} : (ℙ -> A) -> SProp :=
| retε : forall x : A, Shε (fun _ => x)
| askε : forall (i : I) (k : O i -> ℙ -> A),
  (forall o, Shε (k o)) -> Shε (fun α => k (α i) α)
.

Definition eval {A} (x : Shf A) (α : ℙ) : A.
Proof.
unshelve refine (
Shf_rect A (fun _ => A) (fun x => x) (fun i k r => r (α i)) _ x
).
{ clear; intros; destruct eqn; reflexivity. }
Defined.

Lemma evalε : forall A (x : Shf A), Shε (eval x).
Proof.
intros A x.
simple refine (
Shf_sind A (fun x => Shε (eval x)) _ _ x
); clear x; simpl.
+ intros x.
  apply (retε x).
+ intros i k kε.
  apply (askε i (fun o => eval (ask i k))).
  apply kε.
Qed.

Lemma eval_retract : forall A (x : Shf A) (α : ℙ),
  ret (eval x α) = x.
Proof.
intros A x α.
apply uip.
refine (
Shf_sind A (fun x => seq (ret (eval x α)) x) _ _ x
); clear x; simpl.
+ reflexivity.
+ intros i k r.
  change (eval (ask i k) α) with (eval (k (α i)) α).
  change k with (fun _ : O i => k (α i)) at 2.
  rewrite eqn.
  apply r.
Qed.

Section Permut.

Variable A : Type.
Variable i j : I.
Variable k : O i -> O j -> Shf A.

Lemma permut_equiv :
  ask i (fun o => ask j (fun q => k o q)) = ask j (fun q => ask i (fun o => k o q)).
Proof.
match goal with [ |- ?p = ?q ] => rewrite <- (eqn i q) end.
f_equal; apply sfunext; intros o.
f_equal; apply sfunext; intros q.
change (fun o' => k o' q) with (fun _ : O i => k o q).
rewrite eqn; reflexivity.
Qed.

End Permut.

Inductive inhabited (A : Type) : SProp := inhabits : A -> inhabited A.

Definition unique_choice :=
  forall (A : Type) (hA : forall x y : A, x = y), inhabited A -> A.

Lemma unique_eval_ret : forall A (p : Shf A) (x : A),
  eval p = (fun _ : ℙ => x) -> p = ret x.
Proof.
intros A p x e.
apply uip.
revert x e.
refine (Shf_sind A (fun p => forall x, eval p = (fun _ => x) -> seq p (ret x)) _ _ p); clear p.
+ intros x₀ x e.
  unfold eval in e.
  cbn in *.
Admitted.

Lemma unique_eval_inv : forall A (x : ℙ -> A) (xε : Shε x)
  (p q : {x₀ : Shf A | eval x₀ = x }), p = q.
Proof.
intros A x xε [p hp] [q hq].
cut (p = q).
+ intros e; revert hq; destruct e; intros hq.
  assert (e : hp = hq) by apply uip₀.
  destruct e; reflexivity.
+ apply uip.
  revert p x xε hp q hq.
  refine (Shf_sind A _ _ _).
  - intros x₀ x xε hp q hq.
    compute in hp.
    revert q x₀ x xε hp hq.
    refine (Shf_sind A _ _ _).
    * intros x₁ x₂ x xε hp hq.
      compute in hq.
      revert x₁ x₂ hp hq.
      induction xε; intros x₁ x₂ hp hq.
      

Admitted.

Definition sreify {A : Type} {U : unique_choice} (x : ℙ -> A) (xε : Shε x) :
  inhabited {x₀ : Shf A | eval x₀ = x }.
Proof.
induction xε.
+ constructor.
  exists (ret x); reflexivity.
+ constructor.
  unshelve eexists.
  - refine (ask i (fun o => _)).
    specialize (H o).
    apply U in H; [|intros; apply unique_eval_inv, s].
    destruct H as [x₀ Hx].
    exact x₀.
  - simpl.
    apply sfunext; intros α.
    match goal with [ |- context [ask i ?k ] ] =>
      change k with (fun _ : O i => k (α i))
    end; simpl.
    rewrite eqn.
    destruct U.
    rewrite e; reflexivity.
Qed.
