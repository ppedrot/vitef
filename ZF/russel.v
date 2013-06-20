Require Import Setoid Morphisms Relations Wellfounded.

(* Definition em := forall A, {A} + {~ A}.
Definition choice := forall A, inhabited A -> A.

Definition classically A := em -> choice -> A.

Definition lift {A} (x : A) : classically A := fun _ _ => x.
Definition bind {A B} (m : classically A) (f : A -> classically B) : classically B :=
  fun em c => f (m em c) em c.

Definition choose {A} {P : A -> Prop} : (exists x, P x) -> classically {x | P x} :=
  fun Hex _ C => C _ (let (x, Hx) := Hex in inhabits (exist _ x Hx)).

Definition Pbind {A} (m : classically A) (f : A -> Prop) : Prop :=
  forall em c, f (m em c).

Notation "'have' x := t 'in' u" := (Pbind t (fun x => u)) (at level 100, t at level 100).
*)

Section Equipotence.

Record injection_def (x y : V) (f : V) := {
  injection_def_fun : function_def x y f;
  injection_def_inj : forall u1 u2 v, u1 ∈ x -> u2 ∈ x -> tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

End Equipotence.

Section Cantor_Bernstein.


End Cantor_Bernstein.

Section Ordinal.


(* The proper class of sets not containing themselves. *)
Definition RT : Type := {x:V | ~V_rel x x}.

Theorem Russell_paradox : False.
 (* Define the Russell set. This is the key step that causes universe
inconsistency.
    If we defined this at top-level, it would already fail. *)
 set (russell := V_const (fun x:RT => proj1_sig x)).

 (* Show that V_rel x russell is exactly the negation of V_rel x x. *)
 assert (russell_rel : forall x:V, V_rel x russell -> ~V_rel x x).
   intros x H. inversion H using V_rel_inv. exact (@proj2_sig _ _).
 assert (russell_rel_rev : forall x:V, ~V_rel x x -> V_rel x russell).
   intros x H. change x with (proj1_sig (exist _ x H : RT)). apply V_rel_def.

 (* Show that the Russell set fails to contain itself. *)
 assert (Hrussell1 : ~V_rel russell russell).
   intro H. assert (H0 := russell_rel _ H). exact (H0 H).

 (* Therefore, the Russell set contains itself. *)
 assert (Hrussell2 : V_rel russell russell).
   exact (russell_rel_rev _ Hrussell1).

 (* Thus, contradiction. *)
 exact (Hrussell1 Hrussell2). (* Coq reports "Proof completed." *)

Show Proof. (* We've generated a complete proof term... *)
Qed. (* Now the typechecking core discovers our mistake: Universe
