Require Setoid.

Definition ext := forall A (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

Section Rlist.

Variable S : Type.

Inductive slist A :=
| SNode : (S -> snode A * S) -> slist A

with snode A :=
| SNil : snode A
| SCons : A -> slist A -> snode A.

Arguments SNode [A] k.
Arguments SNil [A].
Arguments SCons [A] x l.

Fixpoint map {A B} (f : A -> B) (l : slist A) : slist B :=
match l with
| SNode k => SNode (fun s => match k s with (n, s) => (map_node f n, s) end)
end

with map_node {A B} (f : A -> B) (n : snode A) : snode B :=
match n with
| SNil => SNil
| SCons x l => SCons (f x) (map f l)
end.

Definition nil {A} : slist A := SNode (fun s => (SNil, s)).
Definition ret {A} (x : A) : slist A := SNode (fun s => (SCons x nil, s)).

Fixpoint run {A} (l : slist A) (s : S) {struct l} : list A * S :=
match l with
| SNode k => match k s with (n, s) => run_node n s end
end

with run_node {A} (n : snode A) (s : S) {struct n} : list A * S :=
match n with
| SNil => (Datatypes.nil, s)
| SCons x l => match run l s with (l, s) => (Datatypes.cons x l, s) end
end.

Fixpoint app {A} (l1 l2 : slist A) : slist A :=
match l1 with
| SNode k => SNode (fun s => match k s with (n1, s) => app_node n1 l2 s end)
end

with app_node {A} (n1 : snode A) (l2 : slist A) : S -> snode A * S :=
match n1 with
| SNil => match l2 with SNode k => k end
| SCons x l1 => fun s => (SCons x (app l1 l2), s)
end.

Fixpoint bind {A B} (f : A -> slist B) (l : slist A) : slist B :=
match l with
| SNode k => SNode (fun s => match k s with (n, s) => bind_node f n s end)
end

with bind_node {A B} (f : A -> slist B) (n : snode A) : S -> snode B * S :=
match n with
| SNil => fun s => (SNil, s)
| SCons x l => fun s => match app (f x) (bind f l) with SNode k => k s end
end.

Section Equality.

Import RelationClasses.

Variable A : Type.
Variable eq : A -> A -> Prop.
Variable Equivalence_eq : Equivalence eq.

Fixpoint slist_eq (l1 l2 : slist A) {struct l1} : Prop :=
match l1, l2 with
| SNode k1, SNode k2 =>
  forall s, match (k1 s), (k2 s) with (n1, s1), (n2, s2) => s1 = s2 /\ snode_eq n1 n2 end
end

with snode_eq (n1 n2 : snode A) {struct n1} : Prop :=
match n1, n2 with
| SNil, SNil => True
| SCons x l1, SCons y l2 => eq x y /\ slist_eq l1 l2
| _, _ => False
end.

Local Notation "x == y" := (slist_eq x y) (at level 70, no associativity).

Lemma Reflexive_slist_eq : forall l, l == l
with Reflexive_snode_eq : forall n, snode_eq n n.
Proof.
+ intros [k] s; simpl; destruct (k s) as [n s']; split.
  - reflexivity.
  - apply Reflexive_snode_eq.
+ intros [|x l]; simpl; constructor.
  - reflexivity.
  - apply Reflexive_slist_eq.
Qed.

Lemma Symmetric_slist_eq : forall l1 l2, l1 == l2 -> l2 == l1
with Symmetric_snode_eq : forall n1 n2, snode_eq n1 n2 -> snode_eq n2 n1.
Proof.
+ intros [k1] [k2] H s; simpl in *.
  specialize (H s).
  destruct (k1 s) as [n1 s1], (k2 s) as [n2 s2]; destruct H as [Hs Hn]; split.
  - symmetry; assumption.
  - apply Symmetric_snode_eq; assumption.
+ intros [|x1 l1] [|x2 l2]; simpl; trivial.
  intros [Hx Hl]; split.
  - symmetry; assumption.
  - apply Symmetric_slist_eq; assumption.
Qed.

Lemma Transitive_slist_eq : forall l1 l2 l3, l1 == l2 -> l2 == l3 -> l1 == l3
with Transitive_snode_eq : forall n1 n2 n3, snode_eq n1 n2 -> snode_eq n2 n3 -> snode_eq n1 n3.
Proof.
+ intros [k1] [k2] [k3] Hl Hr s; simpl in *.
  specialize (Hl s); specialize (Hr s).
  destruct (k1 s) as [n1 s1], (k2 s) as [n2 s2]; destruct (k3 s) as [n3 s3].
  destruct Hl as [Hsl Hnl], Hr as [Hsr Hnr]; split.
  - transitivity s2; assumption.
  - apply (Transitive_snode_eq n1 n2 n3); assumption.
+ intros [|x1 l1] [|x2 l2] [|x3 l3]; simpl; try (intros; trivial || contradiction).
  intros [Hxl Hll] [Hxr Hlr]; split.
  - transitivity x2; assumption.
  - apply (Transitive_slist_eq l1 l2 l3); assumption.
Qed.

Instance Equivalence_slist_eq : Equivalence slist_eq := {|
  Equivalence_Reflexive := Reflexive_slist_eq;
  Equivalence_Symmetric := Symmetric_slist_eq;
  Equivalence_Transitive := Transitive_slist_eq
|}.

Instance Equivalence_snode_eq : Equivalence snode_eq := {|
  Equivalence_Reflexive := Reflexive_snode_eq;
  Equivalence_Symmetric := Symmetric_snode_eq;
  Equivalence_Transitive := Transitive_snode_eq
|}.

Import Equivalence.
Open Scope equiv_scope.

Lemma SCons_inj : forall x1 x2 l1 l2, SCons x1 l1 === SCons x2 l2 -> x1 === x2 /\ l1 === l2.
Proof.
intros x1 x2 l1 l2 H; exact H.
Qed.

Lemma app_nil_l : forall (l : slist A), app nil l === l.
Proof.
intros l; simpl; destruct l; intros s.
destruct (p s); split; reflexivity.
Qed.

Lemma app_nil_r : forall (l : slist A), app l nil === l
with app_node_nil_r : forall (n : snode A) s, match app_node n nil s with (n', s') => s' = s /\ n' === n end.
Proof.
+ intros [k] s; cbn.
  destruct (k s) as [n s']; specialize (app_node_nil_r n s').
  apply app_node_nil_r.
+ intros [|x l] s; simpl.
  - split; reflexivity.
  - split; [reflexivity|].
    split; [reflexivity|]; apply app_nil_r.
Qed.

Lemma bind_id_l : forall (l : slist A), bind ret l === l
with bind_node_id_l : forall (n : snode A) s, match bind_node ret n s with (n', s') => s' = s /\ n' === n end.
Proof.
+ intros [k] s; simpl.
  destruct (k s) as [n s']; specialize (bind_node_id_l n s').
  apply bind_node_id_l.
+ intros [|x l] s.
  - split; reflexivity.
  - split; [reflexivity|].
    split; [reflexivity|].
    specialize (bind_id_l l).
    rewrite app_nil_l, bind_id_l; reflexivity.
Qed.

End Equality.

Section ExtEq.

Variable extensionality : ext.

Lemma slist_ext_eq : forall A (l1 l2 : slist A), slist_eq _ eq l1 l2 -> l1 = l2.
Proof.
fix F 2.
intros A [k1] [k2] Heq; f_equal.
apply extensionality; intros s; specialize (Heq s).
destruct (k1 s) as [n1 s1]; destruct (k2 s) as [n2 s2].
fold (snode_eq _ eq n1 n2) in Heq; destruct Heq as [Hrw Heq].
f_equal; [clear Hrw|assumption].
destruct n1 as [|x1 l1], n2 as [|x2 l2].
+ reflexivity.
+ elim Heq.
+ elim Heq.
+ destruct Heq as [Hrw Heq]; fold (slist_eq _ eq l1 l2) in Heq.
  f_equal; [assumption|apply F, Heq].
Qed.

End ExtEq.


Lemma app_nil_l : forall A (l : slist A), app nil l = l.
Proof.
intros A l; simpl.
destruct l; reflexivity.
Qed.

Lemma app_nil_r : ext -> forall A (l : slist A), app l nil = l
with app_node_nil_r : ext -> forall A (n : snode A) s, app_node n nil s = (n, s).
Proof.
+ intros Hext A [n]; simpl.
  f_equal; apply Hext; intros s.
  destruct (n s) as [l s']; simpl in *.
  apply app_node_nil_r; assumption.
+ intros Hext A [|x l] s.
  - reflexivity.
  - simpl; repeat f_equal.
    apply app_nil_r; assumption.
Qed.

Lemma bind_id_l : ext -> forall A (l : slist A), bind ret l = l
with bind_node_id_l : ext -> forall A (n : snode A) s, bind_node ret n s = (n, s).
Proof.
+ intros Hext A [n]; simpl; f_equal.
  apply Hext; intros s.
  destruct (n s) as [l s'].
  apply bind_node_id_l; assumption.
+ intros Hext A [|x l] s; simpl.
  - reflexivity.
  - repeat f_equal.
    specialize (bind_id_l Hext A l); clear - Hext bind_id_l.
    destruct l as [n]; f_equal; apply Hext; intros s.
    rewrite bind_id_l; reflexivity.
Qed.

Lemma bind_id_r : ext -> forall A B (f : A -> slist B) (x : A), bind f (ret x) = f x.
Proof.
intros Hext A B f x; simpl.
destruct (f x); clear f x; f_equal.
apply Hext; intros s; simpl.
destruct (p s) as [n s']; simpl.
rewrite app_node_nil_r; trivial.
Qed.

Lemma bind_assoc : ext -> forall A B C (f : A -> slist B) (g : B -> slist C) l,
  bind g (bind f l) = bind (fun x => bind g (f x)) l
with bind_node_assoc : ext -> forall A B C (f : A -> slist B) (g : B -> slist C) n s,
match bind_node f n s with (n, s) => bind_node g n s end =
bind_node (fun x : A => bind g (f x)) n s.
Proof.
+ intros Hext A B C f g [n].
  simpl; f_equal; apply Hext; intros s.
  destruct (n s) as [l s']; simpl.
  apply bind_node_assoc; assumption.
+ intros Hext A B C f g [|x l] s; simpl.
  - reflexivity.
  - rewrite <- bind_assoc; [|assumption].
    