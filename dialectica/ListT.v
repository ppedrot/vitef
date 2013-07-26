Require Extensionality.

(** Implementation of the List monad transformer in Coq. *)

Set Implicit Arguments.

(** We use Mersenne induction to ensure that even if T may not be positive, that
    does not impede the writing of such a type. *)

Inductive listT R (T : Type -> Type) A :=
| NodeT : forall S, (S -> R + nodeT R T A) -> T S -> listT R T A

with nodeT R (T : Type -> Type) A :=
| Nil : nodeT R T A
| Cons : A -> listT R T A -> nodeT R T A.

Arguments Nil [_ _ _].

Fixpoint map {R T A B} (f : A -> B) (l : listT R T A) : listT R T B
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
Defined.

Section Ops.

Context (R : Type) (T : Type -> Type).
Variable lift : forall {A}, A -> T A.
Variable bind : forall {A B}, (A -> T B) -> (T A -> T B).

Fixpoint fold_right {A B} (f : B -> A -> A) (accu : T A) (l : listT R T B) : T (R + A)
with fold_right_node {A B} (f : B -> A -> A) (accu : T A) (n : nodeT R T B) : T (R + A).
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
    { apply lift, inr, (f x accu). }
Defined.

End Ops.
