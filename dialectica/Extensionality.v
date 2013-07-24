Definition extensionality := forall A (B : A -> Type) (f g : forall x, B x),
  (forall x : A, f x = g x) -> f = g.

Definition ext_eq {A} (x y : A) := extensionality -> x = y.

Notation "x ≅ y" := (ext_eq x y) (at level 70).
