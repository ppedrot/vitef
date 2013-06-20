Require Import BinPos.

Inductive t A :=
| tI : A -> t (prod A A) -> t A
| tO : t (prod A A) -> t A
| tH : A -> t A.

Arguments tH {A} _.
Arguments tO {A} _.
Arguments tI {A} _ _.

Fixpoint succ {A} (x : A) (T : t A) : t A :=
match T with
| tH y => tO (tH (x, y))
| tO T => tI x T
| tI y T => tO (succ (x, y) T)
end.

Fixpoint pred_double {A} (T : t (A * A)) : prod A (t A) :=
match T with
| tH (x, y) => (x, tH y)
| tO T => match pred_double T with ((x, y), T) => (x, tI y T) end
| tI (x, y) T => (x, tI y (tO T))
end.

Fixpoint pred {A} (T : t A) : prod A (t A) :=
match T with
| tH x => (x, tH x)
| tO T => pred_double T
| tI x T => (x, tO T)
end.

Fixpoint hd {A} (T : t A) :=
match T with
| tH x => x
| tO T => fst (hd T)
| tI x _ => x
end.

Definition tl {A} (T : t A) := snd (pred T).
Definition tl_double {A} (T : t (A * A)) := snd (pred_double T).

Lemma hd_tl_double : forall A (T : t (prod A A)),
  snd (hd T) = hd (snd (pred_double T)) /\
  fst (hd T) = fst (pred_double T).
Proof.
fix F 2; intros A [p T|T|]; [specialize (F _ T)|specialize (F _ T)|clear F]; simpl.
+ destruct p as [x1 x2]; simpl; split; reflexivity.
+ set (R := pred_double T) in *; destruct R as [[r1 r2] R]; simpl in *.
  destruct F as [Fl Fr]; split; rewrite Fr; reflexivity.
+ destruct p; split; reflexivity.
Qed.

Lemma pred_double_spec : forall A (T : t (prod A A)), pred_double T = pred (tO T).
Proof.
intros A [p T|T|]; simpl.
+ destruct p as [x y]; reflexivity.
+ reflexivity.
+ intros [x y]; reflexivity.
Qed.

Lemma pred_succ : forall A x (T : t A), pred (succ x T) = (x, T).
Proof.
intros A x T; destruct T; simpl; try reflexivity.
revert A x a T; fix F 4; intros A a b T.
destruct T as [y T|T|]; simpl; try reflexivity.
specialize (F (prod A A) (a, b) y T); rewrite F; reflexivity.
Qed.

Lemma hd_succ : forall A x (T : t A), hd (succ x T) = x.
Proof.
intros A x T; revert x; induction T as [y T|T|]; intros x; simpl; try reflexivity.
rewrite IHT; reflexivity.
Qed.

Lemma tl_succ : forall A x (T : t A), tl (succ x T) = T.
Proof.
intros A x T; unfold tl; rewrite pred_succ; reflexivity.
Qed.

Fixpoint peano_rect A (P : t A -> Type)
  (c1 : forall x : A, P (tH x)) (cS : forall x T, P T -> P (succ x T)) (T : t A) : P T :=
  let F :=
    peano_rect (prod A A) (fun T => P (tO T))
    (fun p => match p with (x, y) => cS x _ (c1 y) end)
    (fun p T r => match p with (x, y) => cS x _ (cS y _ r) end) in
  match T return P T with
  | tH x => c1 x
  | tO T => F T
  | tI x T => cS x (tO T) (F T)
  end.

(* Inductive index : forall {A} (i : positive) (x : A) (T : t A), Prop :=
| index_H : forall A (x : A), index xH x (tH x)
| index_I : forall A (x : A) T, index xH x (tI x T)
| index_IL : forall A i (x y z : A) T, index i (x, y) T -> index (xO i) x (tI z T)
| index_IR : forall A i (x y z : A) T, index i (x, y) T -> index (xI i) y (tI z T)
| index_OL : forall A i (x y : A) T, index i (x, y) T -> index (Pos.pred_double i) x (tO T)
| index_OR : forall A i (x y : A) T, index i (x, y) T -> index (xO i) y (tO T). *)

Fixpoint nth {A} i (T : t A) : option A :=
match T with
| tH x =>
  match i with
  | xH => Some x
  | _ => None
  end
| tO T =>
  match i with
  | xH => Some (fst (hd T))
  | xO i =>
    match nth i T with
    | None => None
    | Some (_, y) => Some y
    end
  | xI i =>
    match nth (Pos.succ i) T with
    | None => None
    | Some (x, _) => Some x
    end
  end
| tI z T =>
  match i with
  | xH => Some z
  | xO i =>
    match nth i T with
    | None => None
    | Some (x, _) => Some x
    end
  | xI i =>
    match nth i T with
    | None => None
    | Some (_, y) => Some y
    end
  end
end.

Lemma nth_1_1 : forall A (x : A), nth 1 (tH x) = Some x.
Proof.
reflexivity.
Qed.

Lemma nth_1_succ : forall A (x : A) T, nth 1 (succ x T) = Some x.
Proof.
intros A x T; revert x; induction T as [A y T IH|A T IH|A]; intros x; simpl; try reflexivity.
rewrite hd_succ; reflexivity.
Qed.

Lemma nth_succ_1 : forall A i (x : A), nth (Pos.succ i) (tH x) = None.
Proof.
intros A i x; destruct i; simpl; reflexivity.
Qed.

Lemma nth_succ_succ : forall A i (x : A) T, nth (Pos.succ i) (succ x T) = nth i T.
Proof.
intros A i x T; revert i x.
induction T as [A z T IH|A T IH|A z]; intros i x; simpl.
+ destruct i as [i|i|]; simpl.
  { rewrite IH; reflexivity. }
  { rewrite IH; reflexivity. }
  { rewrite nth_1_succ; reflexivity. }
+ destruct i; simpl; try reflexivity.
  destruct T as [[? ?] T|T|[? ?]]; simpl; try reflexivity.
  destruct (hd T) as [[? ?] ?]; reflexivity.
+ destruct i; simpl.
  - remember (Pos.succ i) as j; destruct j; try reflexivity.
    elim (Pos.succ_not_1 i); symmetry; assumption.
  - remember (Pos.succ i) as j; destruct j; try reflexivity.
    elim (Pos.succ_not_1 i); symmetry; assumption.
  - reflexivity.
Qed.

Lemma nth_hd : forall A (T : t A), nth 1 T = Some (hd T).
Proof.
destruct T; reflexivity.
Qed.

Fixpoint fold_right {A B} (f : A -> B -> B) (T : t A) (accu : B) : B :=
match T with
| tH x => f x accu
| tO T => fold_right (fun (p : prod A A) accu => let (x, y) := p in f x (f y accu)) T accu
| tI x T => f x (fold_right (fun (p : prod A A) accu => let (x, y) := p in f x (f y accu)) T accu)
end.

Lemma fold_right_1 : forall A B (x : A) f (accu : B),
  fold_right f (tH x) accu = f x accu.
Proof.
reflexivity.
Qed.

Lemma fold_right_succ : forall A B x (T : t A) f (accu : B),
  fold_right f (succ x T) accu = f x (fold_right f T accu).
Proof.
intros A B x T; revert B x; induction T; intros B x f accu; simpl in *.
+ rewrite IHT; reflexivity.
+ reflexivity.
+ reflexivity.
Qed.

Fixpoint fold_left {A B} (f : A -> B -> A) (accu : A) (T : t B) : A :=
match T with
| tH x => f accu x
| tO T => fold_left (fun accu (p : prod B B) => let (x, y) := p in f (f accu x) y) accu T
| tI x T =>
  fold_left (fun accu (p : prod B B) => let (x, y) := p in f (f accu x) y) (f accu x) T
end.

Lemma fold_left_1 : forall A B (x : A) f (accu : B),
  fold_left f accu (tH x) = f accu x.
Proof.
reflexivity.
Qed.

Lemma fold_left_succ : forall A B x (T : t A) f (accu : B),
  fold_left f accu (succ x T) = fold_left f (f accu x) T.
Proof.
intros A B x T; revert B x; induction T; intros B x f accu; simpl in *.
+ rewrite IHT; reflexivity.
+ reflexivity.
+ reflexivity.
Qed.

Fixpoint map {A B} (f : A -> B) (T : t A) : t B :=
match T with
| tH x => tH (f x)
| tO T => tO (map (fun p => match p with (x, y) => (f x, f y) end) T)
| tI x T => tI (f x) (map (fun p => match p with (x, y) => (f x, f y) end) T)
end.

Lemma map_1 : forall A B (f : A -> B) (x : A), map f (tH x) = tH (f x).
Proof.
reflexivity.
Qed.

Lemma map_succ : forall A B (f : A -> B) (x : A) (T : t A), map f (succ x T) = succ (f x) (map f T).
Proof.
intros A B f x T; revert B x f; induction T as [A y T IHT|A T IHT|A]; intros B x f; simpl.
+ rewrite IHT; reflexivity.
+ reflexivity.
+ reflexivity.
Qed.

Fixpoint length {A} (T : t A) : positive :=
match T with
| tH _ => xH
| tO T => xO (length T)
| tI _ T => xI (length T)
end.

Lemma length_1 : forall A (x : A), length (tH x) = xH.
Proof.
reflexivity.
Qed.

Lemma length_succ : forall A (x : A) (T : t A), length (succ x T) = Pos.succ (length T).
Proof.
intros A x T; revert x; induction T as [A y T IHT|A T IHT|A]; intros x; simpl.
+ rewrite IHT; reflexivity.
+ reflexivity.
+ reflexivity.
Qed.

Fixpoint update_aux {A} i (T : t A) (k : A -> A) : t A :=
match T with
| tH y =>
  match i with
  | xH => tH (k y)
  | _ => T
  end
| tO T =>
  match i with
  | xH =>
    let k (p : prod A A) := let (x, y) := p in (k x, y) in
    tO (update_aux i T k)
  | xO i =>
    let k (p : prod A A) := let (x, y) := p in (x, k y) in
    tO (update_aux i T k)
  | xI i =>
    let k (p : prod A A) := let (x, y) := p in (k x, y) in
    tO (update_aux (Pos.succ i) T k)
  end
| tI y T =>
  match i with
  | xH => tI (k y) T
  | xO i =>
    let k (p : prod A A) := let (x, y) := p in (k x, y) in
    tI y (update_aux i T k)
  | xI i =>
    let k (p : prod A A) := let (x, y) := p in (x, k y) in
    tI y (update_aux i T k)
  end
end.

Definition update {A} i (x : A) T : t A := update_aux i T (fun _ => x).

Lemma update_aux_1 : forall A (x : A) T k,
  update_aux 1 (succ x T) k = succ (k x) T.
Proof.
intros A x T; revert x; induction T as [A y T IHT|A T IHT|A y]; intros x k; simpl.
+ rewrite IHT; reflexivity.
+ reflexivity.
+ reflexivity.
Qed.

Lemma update_aux_succ : forall A i (x : A) T k,
  update_aux (Pos.succ i) (succ x T) k = succ x (update_aux i T k).
Proof.
intros A i x T; revert i x; induction T as [A y T IHT|A T IHT|A y]; intros i x k; simpl.
+ destruct i; simpl.
  - rewrite IHT; reflexivity.
  - rewrite IHT; reflexivity.
  - simpl; rewrite update_aux_1; reflexivity.
+ destruct i; simpl; reflexivity.
+ destruct i; simpl; [| |reflexivity].
  - remember (Pos.succ i) as j; destruct j; try reflexivity.
    elim (Pos.succ_not_1 i); symmetry; assumption.
  - remember (Pos.succ i) as j; destruct j; try reflexivity.
    elim (Pos.succ_not_1 i); symmetry; assumption.
Qed.

Lemma update_1_succ : forall A (x y : A) T,
  update 1 x (succ y T) = succ x T.
Proof.
intros A x y T; unfold update; rewrite update_aux_1; reflexivity.
Qed.

Lemma update_1_1 : forall A (x y : A),
  update 1 x (tH y) = tH x.
Proof.
reflexivity.
Qed.

Lemma update_succ_succ : forall A i (x y : A) T,
  update (Pos.succ i) x (succ y T) = succ y (update i x T).
Proof.
intros A i x y T; unfold update; rewrite update_aux_succ; reflexivity.
Qed.

Lemma update_succ_1 : forall A i (x y : A),
  update (Pos.succ i) x (tH y) = tH y.
Proof.
intros A i x y; unfold update; destruct i; reflexivity.
Qed.

Fixpoint make {A} p (v : A) : t A :=
match p with
| xH => tH v
| xO p => tO (make p (v, v))
| xI p => tI v (make p (v, v))
end.

Fixpoint to_list {A} (T : t A) : list A := fold_right (@cons _) T nil.

Fixpoint init_aux {A} p r (f : positive -> A) : t A :=
match p with
| xH => tH (f xH)
| xO p =>
  let f p := (f p, f (Pos.add r p)) in
  tO (init_aux p (xO r) f)
| xI p =>
  let v := f xH in
  let f p := (f (Pos.add r p), f (Pos.add (xO r) p)) in
  tI v (init_aux p (xO r) f)
end.

Definition init {A} p f := @init_aux A p 1 f.

Inductive Nth : forall {A} (i : positive) (x : A) (T : t A), Prop :=
| Nth_H : forall A (x : A), Nth xH x (tH x)
| Nth_I : forall A (x : A) T, Nth xH x (tI x T)
| Nth_IL : forall A i (x y z : A) T, Nth i (x, y) T -> Nth (xO i) x (tI z T)
| Nth_IR : forall A i (x y z : A) T, Nth i (x, y) T -> Nth (xI i) y (tI z T)
| Nth_OL : forall A i (x y : A) T, Nth i (x, y) T -> Nth (Pos.pred_double i) x (tO T)
| Nth_OR : forall A i (x y : A) T, Nth i (x, y) T -> Nth (xO i) y (tO T).

Lemma Nth_nth_spec : forall A i x (T : t A),
  Nth i x T <-> nth i T = Some x.
Proof.
intros A i x T; split; intros H.
+ induction H; try constructor; simpl in *;
  try solve [destruct (nth i T) as [(u, v)|]; congruence].
  destruct i; simpl in *.
  - destruct (nth i~1 T) as [(u, v)|]; congruence. 
  - rewrite Pos.succ_pred_double; destruct (nth i~0 T) as [(u, v)|]; congruence.
  - let H := match goal with [ H : ?t = ?u |- _ ] => H end in
    rewrite nth_hd in H; injection H; intros Hrw; rewrite Hrw; reflexivity.
+ revert i x H; induction T as [A y T IHT|A T IHT|A y]; simpl in *; intros i x H.
  - destruct i; simpl in *.
    { remember (nth i T) as p; destruct p as [(u, v)|]; [|congruence].
      eapply Nth_IR with u, IHT; congruence. }
    { remember (nth i T) as p; destruct p as [(u, v)|]; [|congruence].
      eapply Nth_IL with v, IHT; congruence. }
    { replace x with y by congruence; constructor. }
  - destruct i; simpl in *.
    { remember (nth (Pos.succ i) T) as p; destruct p as [(u, v)|]; [|congruence].
      rewrite <- (Pos.pred_double_succ i); apply Nth_OL with v, IHT; congruence. }
    { remember (nth i T) as p; destruct p as [(u, v)|]; [|congruence].
      eapply Nth_OR with u, IHT; congruence. }
    { remember (hd T) as p; destruct p as (u, v); simpl in *.
      apply (Nth_OL _ 1 x v), IHT; rewrite nth_hd; congruence. }
  - destruct i; simpl in *; try congruence.
    replace x with y by congruence; constructor.
Qed.

(* Lemma Nth_map_spec : forall A B (f : A -> B) i x y (T : t A),
  Nth i y (map f T) <-> (Nth i x T /\ y = f x).
Proof.
intros A B f i x y T.
revert x y f; induction T as [z|z T IHT] using peano_rect; intros x y f.
 *)

Lemma init_aux_nth : forall A p r (f : positive -> A) x i,
  Nth i x (init_aux p r f) <-> (Pos.le i p /\ f (Pos.add p r) = x).
Proof.
intros A p r f x i; split; intros H.
+ remember (init_aux p r f) as T; induction H.
  - split; [apply Pos.le_1_l|].
    
SearchAbout Pos.le.
  apply 
  

Time Eval vm_compute in nth 65535 (init (131072 * 64) id).

Time Eval vm_compute in length (update 65536 xH (init 131072 (fun x => x))).
 *)

Eval vm_compute in nth 65536 (make 65536 tt).
Eval compute in init 4 (fun x => x).

Fixpoint derp_double {A} (T : t (A * A)) : prod (t A) A :=
match T with
| tH (x, y) => (tH x, y)
| tO T =>
  match derp_double T with
  | (T, (x, y)) => (succ , y)
  end
| tI (x, y) T => (tI y (tO T), x)
end.

Fixpoint cuss {A} (T : t A) (x : A) :=
match T with
| 

with cuss_carry {A} (T : t A)

Fixpoint add {A} (T1 T2 : t A) : t A :=
match T1 with
| tH x =>
  match T2 with
  | tH y => tO (tH (x, y))
  | tO T2 => tI x T2
  | tI y T2 => tO (succ (x, y) T2)
  end
| tO T1 =>
  match T2 with
  | tH y => T2
  | tO T2 => tO T2
  | tI y T2 => tO T2
  end
| _ => tH (hd T1)
end.

Print Pos.add.

Lemma toto : forall A B (T1 T2 : t B),
  exists T, forall (f : A -> B -> A) accu,
    fold_left f accu T = fold_left f (fold_left f accu T1) T2.
Proof.
intros A B T1 T2; revert A T2; induction T1 as [A x T1 IHT1|A T1 IHT1|A x]; simpl in *; intros B T2.
+ destruct T2 as [y T2|T2|y].
  
+

(* Lemma update_nth_compat : forall A i (x : A) T, nth i (update i x T) = Some x.
Proof.
induction T using peano_rect.
+ rewrite update_1. *)

(* Print Pos.add.

Fixpoint add {A} (T1 T2 : t A) : t A :=
match T1 with
| tH x =>
  match T2 with
  | tH y => tO (tH (x, y))
  | tO T2 => tI x T2
  | tI y T2 => tO (succ (x, y) T2)
  end
| tO T1 =>
  match T2 with
  | tH y => tH (hd T1)
  | tO T2 =>
  | tI y T2 =>
  end
| _ => tH (hd T1)
end. *)
