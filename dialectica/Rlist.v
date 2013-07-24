Require Import Extensionality.

Set Implicit Arguments.
Unset Elimination Schemes.

Inductive Rlist (R : Type) (A : Type) := rnode : (R -> Rnode R A) -> Rlist R A
with Rnode (R : Type) (A : Type) :=
| rnil : Rnode R A
| rcons : A -> Rlist R A -> Rnode R A.

Definition t R A := Rlist R A.

Arguments rnode [_ _] f.
Arguments rnil [_ _].
Arguments rcons [_ _] x l.

Definition nil {R A} : Rlist R A := rnode (fun _ => rnil).
Definition cons {R A} (x : R -> A) (l : Rlist R A) : Rlist R A :=
  rnode (fun r => rcons (x r) l).

Definition lift {R A} (x : A) := @rnode R A (fun _ => rcons x (rnode (fun _ => rnil))).

Fixpoint map {R A B} (f : A -> B) (l : Rlist R A) : Rlist R B :=
match l with
| rnode n => rnode (fun r => map_node f (n r))
end

with map_node {R A B} (f : A -> B) (n : Rnode R A) :=
match n with
| rnil => rnil
| rcons x l => rcons (f x) (map f l)
end.

Fixpoint set {R S A} (g : S -> R) (l : Rlist R A) : Rlist S A :=
match l with
| rnode n => rnode (fun r => set_node g (n (g r)))
end

with set_node {R S A} (g : S -> R) (n : Rnode R A) :=
match n with
| rnil => rnil
| rcons x l => rcons x (set g l)
end.

Fixpoint run {R A} (l : Rlist R A) (r : R) : list A :=
match l with
| rnode n => run_node (n r) r
end

with run_node {R A} (n : Rnode R A) (r : R) : list A :=
match n with
| rnil => Datatypes.nil
| rcons x l => Datatypes.cons x (run l r)
end.

Fixpoint app {R A} (l1 : Rlist R A) (l2 : Rlist R A) : Rlist R A :=
match l1 with
| rnode n => rnode (fun r => app_node (n r) l2 r)
end

with app_node {R A} (n : Rnode R A) (l2 : Rlist R A) : R -> Rnode R A :=
match n with
| rnil => fun r => match l2 with rnode n => n r end
| rcons x l1 => fun r => rcons x (app l1 l2)
end.

Lemma map_app : forall R A B (f : A -> B) l1 l2,
  @map R A B f (app l1 l2) ≅ app (map f l1) (map f l2)
with map_app_node : forall R A B (f : A -> B) n1 l2 r,
  @map_node R A B f (app_node n1 l2 r) ≅ app_node (map_node f n1) (map f l2) r.
Proof.
+ intros R A B f [n1] l2 Hext; simpl.
  f_equal; apply Hext; intros r; apply map_app_node; assumption.
+ intros R A B f n1 l2 r Hext.
  destruct n1 as [|x l1]; [destruct l2 as [n2]; reflexivity|].
  simpl; f_equal; apply map_app; assumption.
Qed.

Fixpoint concat {R A} (l : Rlist R (Rlist R A)) : Rlist R A :=
match l with
| rnode n => rnode (fun r => concat_node (n r) r)
end

with concat_node {R A} (n : Rnode R (Rlist R A)) : R -> Rnode R A :=
match n with
| rnil => fun _ => rnil
| rcons x l => fun r => match app x (concat l) with rnode n => n r end
end.

Lemma app_assoc : forall R A (l1 l2 l3 : Rlist R A),
  app l1 (app l2 l3) ≅ app (app l1 l2) l3
with app_assoc_node : forall R A (n1 : Rnode R A) (l2 l3 : Rlist R A) r,
  app_node n1 (app l2 l3) r ≅ app_node (app_node n1 l2 r) l3 r.
Proof.
+ intros R A [n1] l2 l3 Hext; simpl.
  f_equal; apply Hext; intros r; apply app_assoc_node; assumption.
+ intros R A [|x l1] l2 l3 r Hext; simpl.
  - destruct l2 as [n2]; reflexivity.
  - rewrite app_assoc; [reflexivity|assumption].
Qed.

Lemma concat_app : forall R A l1 l2,
  @concat R A (app l1 l2) ≅ app (concat l1) (concat l2)
with concat_app_node : forall R A n1 l2 r,
  @concat_node R A (app_node n1 l2 r) r ≅ app_node (concat_node n1 r) (concat l2) r.
Proof.
+ intros R A [n1] l2 Hext; simpl.
  f_equal; apply Hext; intros r; apply concat_app_node; assumption.
+ intros R A [|x l1] l2 r Hext; simpl.
  - destruct l2 as [n2]; reflexivity.
  - rewrite (concat_app _ _ l1); [|assumption].
    destruct x as [n]; simpl.
    apply app_assoc_node; assumption.
Qed.

Lemma concat_map : forall R A (l : Rlist R (Rlist R (Rlist R A))),
  concat (concat l) ≅ concat (map concat l)
with concat_map_node : forall R A (n : Rnode R (Rlist R (Rlist R A))) r,
  concat_node (concat_node n r) r ≅ concat_node (map_node concat n) r.
Proof.
+ intros R A l Hext; destruct l as [n]; simpl.
  f_equal; apply Hext; intros r.
  apply concat_map_node; assumption.
+ intros R A [|x l] r Hext.
  - reflexivity.
  - simpl; rewrite <- concat_map; [|assumption].
    destruct x as [n]; simpl.
    apply concat_app_node; assumption.
Qed.

Fixpoint fold_right {R A B} (f : A -> (R -> B) -> (R -> B)) (accu : R -> B) (l : Rlist R A) (r : R) {struct l} : B :=
match l with
| rnode n => fold_right_node f accu (n r) r
end

with fold_right_node {R A B} (f : A -> (R -> B) -> (R -> B)) (accu : R -> B) (n : Rnode R A) (r : R) {struct n} : B :=
match n with
| rnil => accu r
| rcons x l => f x (fold_right f accu l) r
end.

Lemma map_set : forall R S A B f g l,
  @map S A B f (@set R S A g l) ≅ set g (map f l)
with map_set_node : forall R S A B f g n,
  @map_node S A B f (@set_node R S A g n) ≅ set_node g (map_node f n).
Proof.
+ intros R S A B f g [n] Hext; simpl.
  f_equal; apply Hext; intros s.
  apply map_set_node; assumption.
+ intros R S A B f g [|x l] Hext; simpl.
  - reflexivity.
  - f_equal; apply map_set; assumption.
Qed.

Lemma set_set : forall R S T A f g l,
  @set S T A g (@set R S A f l) ≅ set (fun r => f (g r)) l
with set_set_node : forall R S T A f g n,
  @set_node S T A g (@set_node R S A f n) ≅ set_node (fun r => f (g r)) n.
Proof.
+ intros R S T A f g [n] Hext.
  simpl; f_equal; apply Hext; intros r.
  apply set_set_node; assumption.
+ intros R S T A f g [|x l] Hext; simpl.
  - reflexivity.
  - f_equal; apply set_set; assumption.
Qed.

Lemma map_map : forall R A B C f g l,
  @map R B C g (@map R A B f l) ≅ map (fun x => g (f x)) l
with map_map_node : forall R A B C f g n,
  @map_node R B C g (@map_node R A B f n) ≅ map_node (fun x => g (f x)) n.
Proof.
+ intros R A B C f g [n] Hext.
  simpl; f_equal; apply Hext; intros r.
  apply map_map_node; assumption.
+ intros R A B C f g [|x l] Hext; simpl.
  - reflexivity.
  - f_equal; apply map_map; assumption.
Qed.
