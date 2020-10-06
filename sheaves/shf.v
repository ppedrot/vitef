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

Lemma Prod_isSheaf' : forall (J : site) (A : Type) (B : A -> Type),
  (forall x, isSheaf' J (B x)) -> isSheaf' J (forall x, B x).
Proof.
intros J A B Bε.
unshelve econstructor.
+ refine (fun P i f x => (Bε x).(shf_elt' _ _) P i (fun p => f p x)).
+ intros P i f; cbn.
  apply (Bε x).
  intros p; rewrite (hf p); reflexivity.
Defined.

(** Sheafification *)

Axiom Q : forall (J : site) (A : Type), Type.
Axiom qc : forall {J : site} {A} (P : Prop), J P -> (P -> A) -> Q J A.
Axiom q_eq : forall {J : site} {A : Type}
  (P Q : Prop) (i : J P) (j : J Q) (φ : P -> A) (ψ : Q -> A) (α : P -> Q),
  (forall p, φ p = ψ (α p)) ->
  qc P i φ = qc Q j ψ.

Axiom Q_rect : forall {J : site} {A}
  (F : Q J A -> Type)
  (u : forall P (i : J P) (φ : P -> A), F (qc P i φ))
  (ue : forall P Q (i : J P) (j : J Q) (φ : P -> A) (ψ : Q -> A) (α : P -> Q)
    (h : forall p, φ p = ψ (α p)),
    match q_eq P Q i j φ ψ α h in _ = z return F z with eq_refl => u P i φ end = u Q j ψ ),
  forall (q : Q J A), F q.

Axiom Q_rect_qc : forall J A F u ue P i φ,
  @Q_rect J A F u ue (qc P i φ) = u P i φ.

Definition isSeparated (J : site) (A : Type) :=
  forall P (i : J P) (c : P -> A) (x y : A),
      (forall p : P, x = c p) -> (forall p : P, y = c p) -> x = y.

Lemma isSeparated_Q : forall J (A : Type), isSeparated J (Q J A).
Proof.
intros J A P i c.
unshelve refine (Q_rect (fun x => forall y, (forall p : P, x = c p) -> (forall p : P, y = c p) -> x = y) _ _).
+ intros P' j φ y hx; revert y.
  unshelve refine (Q_rect _ _ _).
  - intros P'' k ψ hy.
    assert (e : forall p : P, qc P' j φ = qc P'' k ψ).
    { intros p; rewrite (hx p), (hy p); reflexivity. }
    apply e.
    apply funext in hx; apply funext in hy.
    rewrite <- hx in hy.
    admit.
  -
Abort.

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
