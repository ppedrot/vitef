Require Import Extensionality.

(** Implementation of the List monad transformer in Coq. *)

Set Implicit Arguments.

(** We use Mersenne induction to ensure that even if T may not be positive, that
    does not impede the writing of such a type. *)

Inductive listT (T : Type -> Type) A :=
| NodeT : forall S, (S -> nodeT T A) -> T S -> listT T A

with nodeT (T : Type -> Type) A :=
| Nil : nodeT T A
| Cons : A -> listT T A -> nodeT T A.

Arguments Nil [_ _].

Fixpoint map {T A B} (f : A -> B) (l : listT T A) : listT T B
with map_node {T A B} (f : A -> B) (n : nodeT T A) : nodeT T B.
Proof.
+ destruct l as [S k n]; exists S.
  - intros s.
    apply (map_node T A B f (k s)).
  - exact n.
+ destruct n as [|x l].
  - apply Nil.
  - apply Cons; [exact (f x)|].
    apply (map _ _ _ f l).
Defined.

(* Fixpoint map {R T A B} (f : A -> B) (l : listT R T A) : listT R T B
with map_node {R T A B} (f : A -> B) (n : nodeT R T A) : nodeT R T B.
Proof.
+ destruct l as [S k n]; exists S.
  - intros s; destruct (k s) as [r|N].
    { left; exact r. }
    { right; apply (map_node _ _ A B f N). }
  - exact n.
+ destruct n as [|x l].
  - apply Nil.
  - apply Cons; [exact (f x)|].
    apply (map _ _ _ _ f l).
Defined.*)

Section Ops.

Context (T : Type -> Type).
Variable lift : forall {A}, A -> T A.
Variable bind : forall {A B}, (A -> T B) -> (T A -> T B).

Fixpoint fold_right {A B} (f : B -> A -> T A) (accu : T A) (l : listT T B) : T A
with fold_right_node {A B} (f : B -> A -> T A) (accu : T A) (n : nodeT T B) : T A.
Proof.
+ destruct l as [S k s].
  apply (@bind S); [clear s|exact s].
  intros s; apply (fold_right_node _ _ f accu (k s)).
+ destruct n as [|x l].
  - exact accu.
  - pose (ans := fold_right _ _ f accu l).
    refine (bind _ ans); clear ans accu; intros accu.
    apply (f x accu).
Defined.

(* Definition collapse {A} (m : T (listT T A)) : listT T A.
Proof.
exists (T unit).
exists (nodeT T A); [intros n; exact n|].
refine (bind _ m).
intros [S k s].
refine (bind _ s); clear s; intros s.
apply lift, (k s).
Defined. *)

Fixpoint app {A} (l1 l2 : listT T A) {struct l1} : listT T A
with app_node {A} (n1 : nodeT T A) (l2 : listT T A) {struct n1} : listT T A.
Proof.
+ destruct l1 as [S k s].
  
  apply app_node.
  apply (app_node _ (k s) l2).
+ destruct n1 as [|x l1].
  


(* Fixpoint fold_right {A B} (f : B -> A -> T A) (accu : T A) (l : listT R T B) : T (R + A)
with fold_right_node {A B} (f : B -> A -> T A) (accu : T A) (n : nodeT R T B) : T (R + A).
Proof.
+ destruct l as [S k s].
  apply (@bind S); [clear s|exact s].
  intros s; destruct (k s) as [r|n].
  - apply lift; exact (inl r).
  - apply (fold_right_node _ _ f accu n).
+ destruct n as [|x l].
  - exact (bind (fun x => lift (inr x)) accu).
  - pose (ans := fold_right _ _ f accu l).
    refine (bind _ ans); clear ans accu; intros [r|accu].
    { apply lift, inl, r. }
    { refine (bind _ (f x accu)); intros ans; apply lift, inr, ans. }
Defined.*)

(*Definition collapse {A} (m : T (listT T A)) : listT T A.
Proof.
exists (PnodeT False T A); [exact inr|].
refine (bind _ m).
intros [S k s].
refine (bind _ s); clear s; intros s.
destruct (k s) as [[]|n]; apply lift, n.
Defined. *)

Definition nil {A} : (listT T A) := NodeT (fun _ => inr Nil) (lift tt).
Definition cons {A} (x : A) (l : listT T A) := NodeT (fun _ => inr (Cons x l)) (lift tt).

Lemma toto : forall A B (f : A -> B) l,
  lift (map f l) ≅ fold_right (fun x accu => lift (cons (f x) accu)) (lift nil) l.
Proof.
intros A B f [S k s] Hext; simpl.

End Ops.
