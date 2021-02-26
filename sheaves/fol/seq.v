Fixpoint fin (n : nat) : Type :=
match n with
| 0 => False
| S m => option (fin m)
end.

Definition fin0 {n : nat} : fin (S n) := None.
Definition finS {n : nat} (p : fin n) : fin (S n) := Some p.

Inductive seq (A : Type) : nat -> Type :=
| seq0 : seq A 0
| seqS : forall n, A -> seq A n -> seq A (S n).

Arguments seq0 {_}.
Arguments seqS {_ _}.

Definition map {A B : Type} {n : nat} (f : A -> B) (v : seq A n) : seq B n :=
(fix F n (v : seq A n) :=
match v in seq _ n return seq B n with
| seq0 => seq0
| seqS x v => seqS (f x) (F _ v)
end) n v.

Lemma seq_map_map : forall {A B C} (n : nat) (f : A -> B) (g : B -> C) (v : seq A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
induction v; cbn; [reflexivity|].
f_equal; apply IHv.
Qed.

Lemma seq_map_ext : forall {A B} (n : nat) (f g : A -> B) (v : seq A n),
  (forall x : A, f x = g x) -> map f v = map g v.
Proof.
induction v; intros H; cbn; [reflexivity|].
f_equal; [apply H|]; apply IHv, H.
Qed.

Fixpoint init {A} {n : nat} (f : fin n -> A) : seq A n :=
match n return (fin n -> A) -> seq A n with
| 0 => fun _ => seq0
| S n => fun f => seqS (f fin0) (@init A n (fun p => f (finS p)))
end f.

Lemma map_init : forall A B n (f : fin n -> A) (g : A -> B),
  map g (init f) = init (fun p => g (f p)).
Proof.
induction n; intros f g; simpl; [reflexivity|].
f_equal; apply IHn.
Qed.

Definition hd {A} {n : nat} (v : seq A (S n)) : A :=
match v in seq _ n return
  match n with 0 => unit | S n => A end
with
| seq0 => tt
| seqS x v => x 
end.

Definition tl {A} {n : nat} (v : seq A (S n)) : seq A n :=
match v in seq _ n return
  match n with 0 => unit | S n => seq A n end
with
| seq0 => tt
| seqS x v => v 
end.

Fixpoint tl_n {A n} (p : nat) : seq A (p + n) -> seq A n :=
match p return seq A (p + n) -> seq A n with
| 0 => fun v => v
| S p => fun v => tl_n p (tl v)
end.

Fixpoint hd_n {A n} (p : nat) : seq A (p + n) -> seq A p :=
match p return seq A (p + n) -> seq A p with
| 0 => fun v => seq0
| S p => fun v =>
  match v in seq _ n return
    match n with 0 => unit | S n => (seq A n -> _) -> seq A (S p) end
  with
  | seq0 => tt
  | seqS x v => fun k => seqS x (k v)
  end (hd_n p)
end.

Fixpoint seq_app {A m n} (v : seq A m) (w : seq A n) : seq A (m + n) :=
match v in seq _ m return seq A n -> seq A (m + n) with
| seq0 => fun w => w
| seqS x v => fun w => seqS x (seq_app v w)
end w.

Lemma seq0_eta : forall A (v : seq A 0), v = seq0.
Proof.
intros A v.
refine (
match v in seq _ n return
  match n return seq A n -> Prop with
  | 0 => fun v => v = seq0
  | S n => fun _ => True
  end v
with
| seq0 => eq_refl
| seqS _ _ => I
end
).
Qed.

Lemma hd_tl : forall A (n : nat) (v : seq A (S n)), v = seqS (hd v) (tl v).
Proof.
intros A n v. 
refine (
match v in seq _ n return
  match n return seq A n -> Prop with
  | 0 => fun _ => True
  | S n => fun (v : seq A (S n)) => v = seqS (hd v) (tl v)
  end v
 with
| seq0 => I
| seqS x v => eq_refl
end
).
Qed.

Lemma hd_tl_n : forall A (p n : nat) (v : seq A (p + n)),
  seq_app (hd_n p v) (tl_n p v) = v.
Proof.
induction p; intros n v; cbn in *; [reflexivity|].
rewrite (hd_tl _ _ v); cbn; rewrite IHp; reflexivity.
Qed.

Fixpoint nth {A n} (v : seq A n) : fin n -> A :=
match v in seq _ n return fin n -> A with
| seq0 =>
  fun p => match p with end
| seqS x v =>
  fun p => match p with
  | None => x
  | Some p => nth v p
  end
end.

Lemma nth_init : forall A (n : nat) (f : fin n -> A) p, nth (init f) p = f p.
Proof.
induction n; cbn.
+ intros f [].
+ intros f [p|]; [|reflexivity].
  apply IHn.
Qed.

Lemma nth_map : forall A B (n : nat) (f : A -> B) (v : seq A n) (p : fin n),
  nth (map f v) p = f (nth v p).
Proof.
induction v; cbn.
+ intros [].
+ intros [p|]; [|reflexivity].
  apply IHv.
Qed.

Lemma nth_ext : forall A n (v w : seq A n),
  (forall p : fin n, nth v p = nth w p) -> v = w.
Proof.
induction n; intros v w e.
+ rewrite (seq0_eta _ v), (seq0_eta _ w); reflexivity.
+ rewrite (hd_tl _ _ v), (hd_tl _ _ w); f_equal.
  - specialize (e None); cbn in e.
    rewrite (hd_tl _ _ v), (hd_tl _ _ w) in e; exact e.
  - apply IHn; intros p.
    specialize (e (Some p)); cbn in e.
    rewrite (hd_tl _ _ v), (hd_tl _ _ w) in e; exact e.
Qed.

Fixpoint zero_p (m : nat) {n : nat} : fin m -> fin (m + n) :=
match m return fin m -> fin (m + n) with
| 0 => fun p => match p with end
| S m => fun p => match p with None => fin0 | Some p => Some (zero_p m p) end
end.

Fixpoint shift_p (m : nat) {n : nat} (p : fin n) : fin (m + n) :=
match m return fin (m + n) with
| 0 => p
| S m => finS (shift_p m p)
end.

Lemma fin_add_rect : forall m n (P : fin (m + n) -> Type),
  (forall p : fin m, P (zero_p _ p)) ->
  (forall p : fin n, P (shift_p _ p)) ->
  forall p : fin (m + n), P p.
Proof.
induction m as [|m IHm]; intros n P Hm Hn p; cbn in *.
+ apply Hn.
+ destruct p as [p|].
  - apply (IHm n (fun p => P (Some p)) (fun p => Hm (Some p)) Hn).
  - apply (Hm None).
Defined.

Lemma nth_zero_p : forall A m n (v : seq A m) (w : seq A n) (p : fin m),
  nth (seq_app v w) (zero_p _ p) = nth v p.
Proof.
induction m; intros n v w p; cbn in *.
+ destruct p.
+ destruct p as [p|]; cbn.
  - rewrite (hd_tl _ _ v); cbn.
    apply IHm.
  - rewrite (hd_tl _ _ v); reflexivity.
Qed.

Lemma nth_shift_p : forall A m n (v : seq A m) (w : seq A n) (p : fin n),
  nth (seq_app v w) (shift_p _ p) = nth w p.
Proof.
induction m; intros n v w p; cbn in *.
+ replace v with (@seq0 A); [reflexivity|].
  symmetry; apply seq0_eta.
+ rewrite (hd_tl _ _ v); cbn.
  apply IHm.
Qed.
