Set Universe Polymorphism.

Module type.

Inductive type :=
| atm : Type -> type
| arr : type -> type -> type
| one : type
| tns : type -> type -> type
| nul : type
| pls : type -> type -> type
.

Fixpoint pure (t : type) : Type :=
match t with
| atm A => A
| arr t u => (pure t) -> (pure u)
| one => unit
| tns t u => prod (pure t) (pure u)
| nul => False
| pls t u => sum (pure t) (pure u)
end.

End type.

Module CBN.

Import type.

Definition ℜ (X : Type) := X.

Fixpoint eval (t : type) R : Type :=
match t with
| atm T => T -> ℜ R
| arr t u => (forall R : Type, eval t R -> ℜ R) * eval u R
| one => ℜ R
| tns t u => ((forall R : Type, eval t R -> ℜ R) * (forall R : Type, eval u R -> ℜ R)) -> ℜ R
| nul => False -> ℜ R
| pls t u => ((forall R : Type, eval t R -> ℜ R) + (forall R : Type, eval u R -> ℜ R)) -> ℜ R
end.

Notation "[ A ⊢ R ]" := (eval A R).

Fixpoint eval_env (Γ : list type) : Type :=
match Γ with
| nil => unit
| cons A Γ => prod (forall R, eval A R -> ℜ R) (eval_env Γ)
end.

Definition seq Γ A := forall R, eval_env Γ -> eval A R -> ℜ R.

Lemma axiom : forall Γ A, seq (cons A Γ) A.
Proof.
intros Γ A R [x γ] k; unfold seq; cbn.
exact (x R k).
Defined.

Lemma wkn : forall Γ A B, seq Γ B -> seq (cons A Γ) B.
Proof.
intros Γ A B p R [_ γ] k; unfold seq; cbn.
refine (p _ γ k).
Defined.

Lemma arr_intro : forall Γ A B, seq (cons A Γ) B -> seq Γ (arr A B).
Proof.
intros Γ A B p R γ [x k].
refine (p _ (x, γ) k).
Defined.

Lemma arr_elim : forall Γ A B, seq Γ (arr A B) -> seq Γ A -> seq Γ B.
Proof.
intros Γ A B p q R γ k.
refine (p _ γ ((fun R => q R γ), k)).
Defined.

Lemma tns_intro : forall Γ A B, seq Γ A -> seq Γ B -> seq Γ (tns A B).
Proof.
intros Γ A B p q R γ k.
refine (k ((fun R => p R γ), (fun R => q R γ))).
Defined.

Lemma tns_elim : forall Γ A B C, seq Γ (tns A B) -> seq (cons A (cons B Γ)) C -> seq Γ C.
Proof.
intros Γ A B C p q R γ k.
refine (p _ γ (fun π => q _ (fst π, (snd π, γ)) k)).
Defined.

Lemma pls_introl : forall Γ A B, seq Γ A -> seq Γ (pls A B).
Proof.
intros Γ A B p R γ k.
refine (k (inl (fun R => p R γ))).
Defined.

Lemma pls_intror : forall Γ A B, seq Γ B -> seq Γ (pls A B).
Proof.
intros Γ A B p R γ k.
refine (k (inr (fun R => p R γ))).
Defined.

Lemma pls_elim : forall Γ A B C, seq Γ (pls A B) -> seq (cons A Γ) C -> seq (cons B Γ) C -> seq Γ C.
Proof.
intros Γ A B C p q r R γ k.
refine (p _ γ (fun π => match π with inl kl => q _ (kl, γ) k | inr kr => r _ (kr, γ) k end)).
Defined.

Lemma one_intro : forall Γ, seq Γ one.
Proof.
intros Γ R γ k; exact k.
Defined.

Lemma nul_elim : forall Γ A, seq Γ nul -> seq Γ A.
Proof.
intros Γ A p R γ k.
refine (p _ γ (fun π => match π with end)).
Defined.

(** Interesting feature *)
Lemma iota_sum_l : forall Γ A B C p q r,
  pls_elim Γ A B C (pls_introl _ _ _ p) q r = arr_elim _ _ _ (arr_intro _ _ _ q) p.
Proof.
intros Γ A B C p q r.
reflexivity.
Qed.

Record run (t : type) : Type := {
  reflect : (forall R, eval t R -> ℜ R) -> pure t;
  reify : pure t -> (forall R, eval t R -> ℜ R)
}.

Lemma runner : forall t, run t.
Proof.
induction t; split; cbn.
+ intros k; refine (k _ (fun x => x)).
+ intros x R k; refine (k x).
+ destruct IHt2 as [IHt2 _], IHt1 as [_ IHt1].
  intros k x; apply IHt2.
  intros R p; apply k; split.
  ++ apply IHt1, x.
  ++ apply p.
+ destruct IHt2 as [_ IHt2], IHt1 as [IHt1 _].
  intros k R [x p].
  refine (IHt2 _ _ p).
  apply k, IHt1, x.
+ intros k; refine (k _ tt).
+ intros [] R x; exact x.
+ destruct IHt2 as [IHt2 _], IHt1 as [IHt1 _].
  intros k; apply k.
  intros [pl pr]; split.
  ++ apply IHt1, pl.
  ++ apply IHt2, pr.
+ destruct IHt2 as [_ IHt2], IHt1 as [_ IHt1].
  intros [x y] R p.
  apply (p (IHt1 x, IHt2 y)).
+ intros k; refine (k _ (False_rect _)).
+ intros [].
+ destruct IHt2 as [IHt2 _], IHt1 as [IHt1 _].
  intros k; apply k.
  intros [pl|pr].
  ++ left; apply IHt1, pl.
  ++ right; apply IHt2, pr.
+ destruct IHt2 as [_ IHt2], IHt1 as [_ IHt1].
  intros [x|y].
  ++ intros R k; apply k; left; apply (IHt1 x).
  ++ intros R k; apply k; right; apply (IHt2 y).
Defined.

End CBN.

Module CBV.

Import type.

Definition ℜ (X : Type) := X.

Fixpoint evalv (t : type) : Type :=
match t with
| atm T => T
| arr t u => forall R : Type, (evalv t) * (evalv u -> ℜ R) -> ℜ R
| one => unit
| tns t u => (evalv t) * (evalv u)
| nul => False
| pls t u => evalv t + evalv u
end.

Definition eval t R := evalv t -> ℜ R.

Notation "[ A ⊢ R ]" := (eval A R).

Fixpoint eval_env (Γ : list type) : Type :=
match Γ with
| nil => unit
| cons A Γ => prod (evalv A) (eval_env Γ)
end.

Definition seqv Γ A := eval_env Γ -> evalv A.
Definition seq Γ A := forall R, eval_env Γ -> eval A R -> ℜ R.

Lemma axiom : forall Γ A, seqv (cons A Γ) A.
Proof.
intros Γ A [x γ]; exact x.
Defined.

Lemma arr_intro : forall Γ A B, seq (cons A Γ) B -> seqv Γ (arr A B).
Proof.
intros Γ A B p γ R [x k].
refine (p _ (x, γ) k).
Defined.

Lemma arr_elim : forall Γ A B, seq Γ (arr A B) -> seq Γ A -> seq Γ B.
Proof.
intros Γ A B p q R γ k.
refine (p _ γ (fun f => f _ (q _ γ (fun x => x), k))).
Defined.

Lemma return_val : forall Γ A, seqv Γ A -> seq Γ A.
Proof.
intros Γ A p R γ k.
refine (k (p γ)).
Defined.

Lemma wkn : forall Γ A B, seq Γ B -> seq (cons A Γ) B.
Proof.
intros Γ A B p R [_ γ] k; unfold seq; cbn.
refine (p _ γ k).
Defined.

Lemma tns_intro : forall Γ A B, seq Γ A -> seq Γ B -> seq Γ (tns A B).
Proof.
intros Γ A B p q R γ k.
refine (k (p _ γ (fun x => x), q _ γ (fun x => x))).
Defined.

Lemma tns_elim : forall Γ A B C, seq Γ (tns A B) -> seq (cons A (cons B Γ)) C -> seq Γ C.
Proof.
intros Γ A B C p q R γ k.
refine (p _ γ (fun π => q _ (fst π, (snd π, γ)) k)).
Defined.

Lemma one_intro : forall Γ, seqv Γ one.
Proof.
intros Γ γ; refine tt.
Defined.

Lemma one_elim : forall Γ A, seq Γ one -> seq Γ A -> seq Γ A.
Proof.
intros Γ A p q R γ k.
refine (p _ γ (fun _ => q _ γ k)).
Defined.

Lemma pls_introl : forall Γ A B, seq Γ A -> seq Γ (pls A B).
Proof.
intros Γ A B p R γ k.
refine (k (inl (p _ γ (fun x => x)))).
Defined.

Lemma pls_intror : forall Γ A B, seq Γ B -> seq Γ (pls A B).
Proof.
intros Γ A B p R γ k.
refine (k (inr (p _ γ (fun x => x)))).
Defined.

Lemma pls_elim : forall Γ A B C, seq Γ (pls A B) -> seq (cons A Γ) C -> seq (cons B Γ) C -> seq Γ C.
Proof.
intros Γ A B C p q r R γ k.
refine (p _ γ (fun π => match π with inl kl => q _ (kl, γ) k | inr kr => r _ (kr, γ) k end)).
Defined.

Lemma nul_elim : forall Γ A, seq Γ nul -> seq Γ A.
Proof.
intros Γ A p R γ k.
refine (p _ γ (fun π => match π with end)).
Defined.

(** Interesting feature *)
Lemma iota_sum_l : forall Γ A B C p q r,
  pls_elim Γ A B C (pls_introl _ _ _ p) q r = arr_elim _ _ _ (return_val _ _ (arr_intro _ _ _ q)) p.
Proof.
intros Γ A B C p q r.
reflexivity.
Qed.

Record run (t : type) : Type := {
  reflect : (forall R : Type, eval t R -> ℜ R) -> pure t;
  reify : pure t -> evalv t
}.

Lemma runner : forall t, run t.
Proof.
induction t; split; cbn.
+ intros k; refine (k _ (fun x => x)).
+ refine (fun x => x).

+ destruct IHt2 as [IHt2 _], IHt1 as [_ IHt1].
  intros k x.
  refine (k _ (fun f => _)).
  refine (let r := f _ (IHt1 x, (fun f => IHt2 (fun _ k => k f))) in _); shelve_unifiable.
  apply r.
+ destruct IHt2 as [_ IHt2], IHt1 as [IHt1 _].
  intros f R [x p].
  refine (p (IHt2 (f (IHt1 (fun _ k => k x))))).

+ intros k; refine (k _ (fun x => x)).
+ intros []; exact tt.

+ destruct IHt2 as [IHt2 _], IHt1 as [IHt1 _].
  intros k; apply k.
  intros [pl pr]; split.
  ++ refine (IHt1 (fun _ k => k pl)).
  ++ refine (IHt2 (fun _ k => k pr)).
+ destruct IHt2 as [_ IHt2], IHt1 as [_ IHt1].
  intros [x y].
  apply ((IHt1 x, IHt2 y)).

+ intros k; refine (k _ (False_rect _)).
+ intros [].

+ destruct IHt2 as [IHt2 _], IHt1 as [IHt1 _].
  intros k; apply k.
  intros [pl|pr].
  ++ left; refine (IHt1 (fun _ k => k pl)).
  ++ right; refine (IHt2 (fun _ k => k pr)).
+ destruct IHt2 as [_ IHt2], IHt1 as [_ IHt1].
  intros [x|y].
  ++ left; apply (IHt1 x).
  ++ right; apply (IHt2 y).
Defined.

End CBV.

Module Delim.

Inductive type :=
| atm : Type -> type
| arr : type -> list type -> type -> type
| btm : type
(* | one : type *)
(* | tns : type -> type -> type *)
(* | nul : type *)
(* | pls : type -> type -> type *)
.

Fixpoint fold {A B} (f : A -> B -> A) (accu : A) (l : list B) : A :=
match l with
| nil => accu
| cons x l => f (fold f accu l) x
end.

Definition ℜ (X : Type) := X.

Fixpoint eval (t : type) R {struct t} : Type :=
match t with
| atm T => T -> ℜ R
| arr t σ u =>
  let fix f σ R : Type := match σ with
  | nil => ℜ R
  | cons t σ => (eval t  (f σ R))
  end in
  (forall R : Type, (eval t (f σ R)) -> ℜ R) * eval u R
| btm => unit
(* | one => ℜ R *)
(* | tns t u => ((forall R : Type, eval t R -> ℜ R) * (forall R : Type, eval u R -> ℜ R)) -> ℜ R *)
(* | nul => False -> ℜ R *)
(* | pls t u => ((forall R : Type, eval t R -> ℜ R) + (forall R : Type, eval u R -> ℜ R)) -> ℜ R *)
end.

Notation "[ A ⊢ R ]" := (eval A R).

Fixpoint peval (σ : list type) R {struct σ} : Type :=
match σ with
| nil => ℜ R
| cons t σ => (eval t (peval σ R))
end.

Fixpoint eval_env (Γ : list (type * list type)) : Type :=
match Γ with
| nil => unit
| cons (A, σ) Γ => prod (forall R, peval (cons A σ) R -> ℜ R) (eval_env Γ)
end.

Definition seq Γ A σ := forall R, eval_env Γ -> peval (cons A σ) R -> ℜ R.

Lemma axiom : forall Γ A σ, seq (cons (A, σ) Γ) A σ.
Proof.
intros Γ A σ R [x γ] k; unfold seq; cbn.
exact (x R k).
Defined.

Lemma wkn : forall Γ A B σ τ, seq Γ B σ -> seq (cons (A, τ) Γ) B σ.
Proof.
intros Γ A B σ τ p R [_ γ] k; unfold seq; cbn.
refine (p _ γ k).
Defined.

Lemma arr_intro : forall Γ A B σ τ, seq (cons (A, τ) Γ) B σ -> seq Γ (arr A τ B) σ.
Proof.
intros Γ A B σ τ p R γ [x k].
refine (p _ (x, γ) k).
Defined.

Lemma arr_elim : forall Γ A B σ τ, seq Γ (arr A τ B) σ -> seq Γ A τ -> seq Γ B σ.
Proof.
intros Γ A B σ τ p q R γ k.
refine (p _ γ ((fun R => q R γ), k)).
Defined.

Lemma settp : forall Γ A σ, seq Γ A (cons A σ) -> seq Γ A σ.
Proof.
intros Γ A σ p R γ k.
refine (p _ γ _).
cbn.
constructor.
Qed.

Lemma getp : forall Γ A σ, seq Γ A σ -> seq Γ btm (cons A σ).
Proof.
intros Γ A σ p R γ k.
refine (p _ γ _).
cbn in k.
cbn.
constructor.
Qed.


Eval compute in seq nil (arr (atm nat) nil (atm bool)) nil.

Lemma arr_elim : forall Γ A B σ τ, seq Γ (arr A τ B) σ-> seq Γ A τ -> seq Γ B σ.
Proof.
intros Γ A B σ τ p q R γ k.
refine (p _ γ ((fun R => q R γ), k)).
Defined.


Lemma tns_intro : forall Γ A B, seq Γ A -> seq Γ B -> seq Γ (tns A B).
Proof.
intros Γ A B p q R γ k.
refine (k ((fun R => p R γ), (fun R => q R γ))).
Defined.

Lemma tns_elim : forall Γ A B C, seq Γ (tns A B) -> seq (cons A (cons B Γ)) C -> seq Γ C.
Proof.
intros Γ A B C p q R γ k.
refine (p _ γ (fun π => q _ (fst π, (snd π, γ)) k)).
Defined.

Fixpoint rseq (Γ : list type) A :=
match Γ with
| nil => A
| cons B Γ => arr B (rseq Γ A)
end.

(*
Lemma reset : forall Γ A, [rseq Γ A ⊢ seq Γ A].
Proof.
intros Γ A; revert Γ; unfold seq; cbn.
induction A; cbn; intros Γ.
+ admit.
+ cbn.
+ admit.
+ admit.
+ admit.
+ admit.
Defined.

 *)
(*
Lemma tns_elim' : forall Γ A B C, seq Γ (tns A B) -> seq (cons A (cons B Γ)) C -> seq Γ C.
Proof.
intros Γ A B C p q R γ k.
specialize (p (prod (seq nil A) (seq nil B)) γ).
cbn in *.
destruct p as [pl pr].
intros [kl kr].
split.
apply kl.
clear.
unfold seq; cbn.
induction A; cbn.
unfold seq in pl, pr.
refine (q _ (_, (_, γ)) k).
clear - pl; intros R k; apply (pl _ tt k).
clear - pr; intros R k; apply (pr _ tt k).
Defined.

*)

Lemma pls_introl : forall Γ A B, seq Γ A -> seq Γ (pls A B).
Proof.
intros Γ A B p R γ k.
refine (k (inl (fun R => p R γ))).
Defined.

Lemma pls_intror : forall Γ A B, seq Γ B -> seq Γ (pls A B).
Proof.
intros Γ A B p R γ k.
refine (k (inr (fun R => p R γ))).
Defined.

Lemma pls_elim : forall Γ A B C, seq Γ (pls A B) -> seq (cons A Γ) C -> seq (cons B Γ) C -> seq Γ C.
Proof.
intros Γ A B C p q r R γ k.
refine (p _ γ (fun π => match π with inl kl => q _ (kl, γ) k | inr kr => r _ (kr, γ) k end)).
Defined.

Lemma one_intro : forall Γ, seq Γ one.
Proof.
intros Γ R γ k; exact k.
Defined.

Lemma nul_elim : forall Γ A, seq Γ nul -> seq Γ A.
Proof.
intros Γ A p R γ k.
refine (p _ γ (fun π => match π with end)).
Defined.

Lemma em : forall A, (seq nil (pls (atm A) (arr (atm A) nul))) -> A + ~ A.
Proof.
intros A Hem.
unfold seq in Hem; cbn in Hem.
specialize (Hem (A + ~ A)%type tt).
apply Hem.
intros [Hl|Hr].
+ left; apply Hl; trivial.
+ right; intros x; apply Hr.
  split; intuition.
Defined.

Lemma callcc : forall A B, (seq nil (arr (arr (arr (atm A) (atm B)) (atm A)) (atm A))) -> ((A -> B) -> A) -> A.
Proof.
intros A B Hcc.
unfold seq in Hcc.
cbn in Hcc.
specialize (Hcc A tt).
intros f.
apply Hcc.
split; [|intuition].
intros R [g k].
apply k, f.
intros x; apply g; intuition.
Defined.
