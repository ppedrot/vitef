Require Import Morphisms Base.

Definition cup x y := union (pair x y).

Instance Proper_cup : Proper (V_eq ==> V_eq ==> V_eq) cup.
Proof.
unfold cup; repeat intro; repeat f_equiv; assumption.
Qed.

Lemma cup_spec : forall x y z, z ∈ cup x y <-> z ∈ x \/ z ∈ y.
Proof.
intros x y z; split; intro H.
+ apply union_spec in H; destruct H as [u [Hu Hm]].
  apply pair_spec in Hm; destruct Hm as [Hm|Hm];
  rewrite <- Hm; intuition.
+ apply union_spec; destruct H as [Hm|Hm].
  - exists x; split; [assumption|apply pair_spec; left; reflexivity].
  - exists y; split; [assumption|apply pair_spec; right; reflexivity].
Qed.

Lemma cup_idem : forall x, cup x x ≅ x.
Proof.
intros x; apply extensionality; apply included_spec; intros z Hz.
+ apply cup_spec in Hz; intuition.
+ apply cup_spec; intuition.
Qed.

Definition cap x y := comprehension x (fun z => z ∈ y).

Instance Proper_cap : Proper (V_eq ==> V_eq ==> V_eq) cap.
Proof.
intros x1 x2 Hx y1 y2 Hy; unfold cap; f_equiv; [assumption|].
intros z1 z2 Hz; rewrite Hy, Hz; reflexivity.
Qed.

Lemma cap_spec : forall x y z, z ∈ cap x y <-> (z ∈ x /\ z ∈ y).
Proof.
intros x y z; split; intros H.
+ apply comprehension_spec in H; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
  assumption.
+ apply comprehension_spec; [|assumption].
  intros x1 x2 Hx; rewrite Hx; reflexivity.
Qed.
