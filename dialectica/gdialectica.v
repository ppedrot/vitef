(** Goedel's "Dialectica" functional interpretation of logic, slightly generalized and
   adapted for Coq.

   As a starting point we take chapter VI, "Goedel's Functional Interpretation", by J.
   Avigad and S. Feferman from "Handbook of Proof Theory", edited by S.R. Buss, published
   by Elsevier Science, 1995. A preliminary draft is available at
   http://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf.

   Author: Andrej Bauer, http://andrej.com/
*)

(** * Basic definitions *)

(** Needed for decidable equality on natural numbers but otherwise we could do without
   [Arith]. *)

Require Import Bool Morphisms Setoid Extensionality.
Require List Rlist.

(** The following line is specific to Coq 8.3, but Coq 8.2 does not seem to be bothered by
   it, so luckily this file is compatible with both versions. *)

Unset Automatic Introduction.

Set Implicit Arguments.

(** We shall allow universal and existential quantification over arbitrary inhabited types.
   The usual interpretation allows quantification over the natural numbers (and possibly
   functionals over the natural numbers), which are of course inhabited. *)

Record Inhabited := inhabit { ty :> Type; member : ty }.

(** The inhabited natural numbers. *)

Definition N := inhabit 0.

(** The inductive type [prp] is a "deep embedding" of the abstract syntax of
   the object language that we shall interpret into Coq. We admit only decidable primitive
   predicates, as is usual in the basic Dialectica variant.

   Our embedding allows us to express "exotic" propositional functions [p : ty -> prp] in
   which the logical structure of [p x] may depend on [x]. Because of this phenomenon we
   will be forced later on to introduce certain type dependencies where there are none in
   the usual Dialectica interpretation. *)

Inductive prp : Type :=
  | atm : forall p : bool, prp
  | pls (A B : prp)
  | tns (A B : prp)
  | bng (A : prp)
  | opp (A : prp)
  | unv : forall (T : Inhabited), (T -> prp) -> prp.

Definition neg A := opp (bng A).
Definition wth A B := opp (pls (opp A) (opp B)).
Definition arr A B := opp (tns A (opp B)).
Definition ext T f := opp (unv T (fun x => opp (f x))).
Definition whn A := opp (bng (opp A)).

(** Convenient notation for the object language. *)

Notation "'[' p ']'" := (atm p).
Notation "¬ x" := (neg x) (at level 70, no associativity).
Notation "x ＆ y" := (wth x y) (at level 74, left associativity).
Notation "x ⊕ y" := (pls x y) (at level 76, left associativity).
Notation "x ⊗ y" := (tns x y) (at level 76, left associativity).
Notation "x ⊸ y" := (arr x y) (at level 78, right associativity).
Notation "! x" := (bng x) (at level 1, format "! x").
Notation "? x" := (whn x) (at level 1, format "? x").
Notation "∀ x : t , p" :=  (@unv t (fun x => p)) (at level 80, x at level 99).
Notation "∃ x : t , p" :=  (@ext t (fun x => p)) (at level 80, x at level 99).

(** printing ==> $\Longrightarrow$ #&rArr;# *)

(** With each proposition [p] we associate the types [W p] and [C p] of "witnesses" and
   "counters", respectively. Think of them as moves in a game between a player [W] and an
   opponent [C]. We make two changes to the standard Dialectica representation.

   First, we use sum for counters of conjunctions, where normally a product is used. This
   gives us symmetry between conjunction and disjunction, simplifies the notorious
   conjunction contraction [and_contr], but complicates the adjunction between implication
   and conjunction. Thomas Streicher pointed out that the change is inessential in the
   sense that we could prove a separate lemma which allows us to pass from counters for [p
   and q] as pairs to counters as elements of a sum (such a lemma relies in decidability
   of the [rel] relation defined below).

   Second, because we allow the structure of a propositional function to depend on the
   argument, we are forced to introduce type dependency into [W p] and [C p] when [p] is a
   quantified statement. This is not a big surprise, but what is a little more surprising
   is that the counters for existentials, [C (existential ty p')], involve a dependency
   not only on [ty] but also on [W (p' x)]. The dependency is needed in the rule
   [exists_elim]. The rest of Dialectica interpetation is not influenced by this change,
   with the exception of the Independence of Premise where we have to impose a condition
   that is not required in the usual interpretation.

   These type-dependecies clearly towards an even more type-dependent Dialectica variant.
   Indeed, we are going to investigate it in a separate file. For now we are just trying
   to faithfully represent the Dialectica interpretation. *)

Variable ctx : Type.
Variable daimon : ctx.

Fixpoint W (p : prp) : Type :=
  (match p with
     | atm p => unit
     | pls p1 p2 => (W p1) + (W p2)
     | tns p1 p2 => W p1 * W p2
     | bng p => W p
     | opp p => C p
     | unv ty p' => (forall x : ty, W (p' x))
   end)%type

with C p :=
  (match p with
     | atm p => ctx
     | pls p1 p2 => (C p1) * (C p2) (* forall b : bool, match b with true => C p1 | false => C p2 end *)
     | tns p1 p2 => (W p1 -> C p2) * (W p2 -> C p1)
     | bng p => Rlist.t (W p) (C p)
     | opp p => W p
     | unv ty p' => { x : ty & C (p' x) }
   end)%type.

(** The relation [rel p w c] is what is usually written as [p_D] in the Dialectica
   interpretation, i.e., the matrix of the interpreted formula.

   In terms of games, [rel p w c] tells whether the player move [w] wins against the
   opponent move [c] in the game determined by the proposition [p].
*)

Definition rel_pls {A B} (R : forall X, W X -> C X -> Prop)
  (w : W (A ⊕ B)) (z : C (A ⊕ B)) :=
match w with
| inl u => R A u (fst z)
| inr v => R B v (snd z)
end.

Definition rel_tns {A B} (R : forall X, W X -> C X -> Prop)
  (w : W (A ⊗ B)) (z : C (A ⊗ B)) :=
match w, z with
| (u, v), (zl, zr) => R A u (zr v) /\ R B v (zl u)
end.

Definition rel_unv {T A} (R : forall X, W X -> C X -> Prop)
  (w : W (∀ x : T, A x)) (z : C (∀ x : T, A x)) :=
match z with
| existT _ t u => R (A t) (w t) u
end.

Definition rel_bng {A} (R : forall X, W X -> C X -> Prop) (u : W (! A)) (z : C (! A)) :=
  Rlist.fold_right (fun x P u => R A u x /\ P u) (fun _ => True) z u.

Definition rel_bng_node {A} (R : forall X, W X -> C X -> Prop) (u : W A) (z : Rlist.Rnode (W A) (C A)) :=
  Rlist.fold_right_node (fun x P u => R A u x /\ P u) (fun _ => True) z u.

Lemma rel_bng_simpl : forall A R (u : W (! A)) (z : W A -> _),
  @rel_bng A R u (Rlist.rnode z) = @rel_bng_node A R u (z u).
Proof.
intros A R u z; unfold rel_bng, rel_bng_node; simpl; reflexivity.
Qed.

Lemma rel_bng_nil : forall A R (u : W (! A)),
  @rel_bng_node A R u Rlist.rnil = True.
Proof.
intros A R u; unfold rel_bng, rel_bng_node; simpl; reflexivity.
Qed.

Lemma rel_bng_cons : forall A R (u : W (! A)) (x : C A) (z : C (! A)),
  @rel_bng_node A R u (Rlist.rcons x z) = (R A u x /\ rel_bng R u z).
Proof.
intros A R u x z; unfold rel_bng, rel_bng_node; simpl; reflexivity.
Qed.

Lemma rel_bng_app : forall A R (u : W (! A)) (zl : C (! A)) (zr : C (! A)),
  @rel_bng A R u (Rlist.app zl zr) <-> @rel_bng A R u zl /\ @rel_bng A R u zr.
Proof.
intros A R u zl zr; revert zl.
refine (
  fix F zl {struct zl} := _
  with F_node (n : Rlist.Rnode _ _) {struct n} : (_ n) := _ for F).
+ destruct zl as [nl]; simpl in *; fold (W A).
  rewrite 2 rel_bng_simpl.
  pattern (nl u); apply F_node.
+ destruct n as [|x zl]; simpl in *.
  - clear F F_node; destruct zr as [nr].
    rewrite rel_bng_nil, rel_bng_simpl; tauto.
  - specialize (F zl).
    rewrite 2 rel_bng_cons; intuition.
Qed.

Fixpoint rel (A : prp) : W A -> C A -> Prop :=
  match A return W A -> C A -> Prop with
    | atm p => (fun _ _ => Is_true p)
    | pls A B => rel_pls rel
    | tns A B => rel_tns rel
    | bng A => rel_bng rel
    | opp A => (fun x u => ~ rel A u x)
    | unv T A => rel_unv rel
  end.

(** The [rel] relation is decidable. This fact is used only in the adjunction between
   conjunction and implication. *)

Theorem rel_decidable (A : prp) (u : W A) (x : C A) : {rel A u x} + {~ (rel A u x)}.
Proof.
intros A u x; induction A; simpl.
+ unfold Is_true.
  induction p; tauto.
+ destruct x as [b1 b2].
  destruct u as [a1 | a2]; simpl; auto.
+ destruct u as [u v]; destruct x as [x y]; simpl.
  specialize (IHA1 u (y v)); specialize (IHA2 v (x u)); tauto.
+ revert x; refine (
  (fix F (x : C (! A)) := _
  with F_node (n : Rlist.Rnode (W A) (C A)) :
    {@rel_bng_node A rel u n} + {~ @rel_bng_node A rel u n}
   := _ for F)).
  - destruct x as [n]; rewrite rel_bng_simpl.
    apply F_node.
  - destruct n as [|x l]; simpl.
    { rewrite rel_bng_nil; left; exact I. }
    { rewrite rel_bng_cons.
      destruct (F l); [|intuition].
      destruct (IHA u x); intuition. }
+ destruct (IHA x u); tauto.
+ destruct x as [t x]; simpl; intuition.
Qed.

(** Of course, a decidable proposition is stable for double negation. *)

Lemma rel_not_not (A : prp) (u : W A) (x : C A) : ~ ~ rel A u x -> rel A u x.
Proof.
  intros p w c H.
  destruct (rel_decidable p w c); tauto.
Qed.

Lemma rel_arr : forall A B (w : W (A ⊸ B)) (z : C (A ⊸ B)),
  (rel (A ⊸ B) w z) <-> (rel A (fst z) (snd w (snd z)) -> rel B (fst w (fst z)) (snd z)).
Proof.
intros A B [wl wr] [zl zr]; split; intros H; simpl in *.
+ intros H'; apply rel_not_not; tauto.
+ tauto.
Qed.

(** The predicate [valid p] is the Dialectica interpretation of [p]. It says that there is
   [w] such that [rel p w c] holds for any [c]. In terms of games semantics this means
   that [W] has a winning strategy (which amounts to a winning move [w]). *)

Notation "⊢ A" := (W A) (at level 89).
Notation "⊣ A" := (C A) (at level 89).

Class Valid {A} (f : ⊢ A) := { valid_spec : forall b : C A, rel A f b }.

Definition app {A B} (f : ⊢ A ⊸ B) (x : ⊢ A) : ⊢ B.
Proof.
intros A B [w z] u; exact (w u).
Defined.

Instance Valid_app : forall {A B} (f : ⊢ A ⊸ B) x, Valid f -> Valid x -> Valid (app f x).
Proof.
intros A B [w z] u [Hf] [Hx]; split; intros b.
specialize (Hf (u, b)); rewrite rel_arr in Hf; simpl in Hf.
apply Hf, Hx.
Qed.

Definition id {A} : ⊢ A ⊸ A.
Proof.
intros A; exact (id, id).
Defined.

Instance Valid_id : forall {A}, Valid (@id A).
Proof.
intros A; split; intros [u x]; simpl in *; tauto.
Qed.

Definition compose {A B C} (f : ⊢ A ⊸ B) (g : ⊢ B ⊸ C) : ⊢ A ⊸ C.
Proof.
intros A B C [fl fr] [gl gr].
split; [intros u; apply gl, fl, u|intros z; apply fr, gr, z].
Defined.

Instance Valid_compose : forall {A B C} (f : ⊢ A ⊸ B) (g : ⊢ B ⊸ C),
  Valid f -> Valid g -> Valid (compose f g).
Proof.
intros A B C [fl fr] [gl gr] [Hf] [Hg]; split; intros [u z].
specialize (Hf (u, gr z)); specialize (Hg (fl u, z)).
rewrite rel_arr; rewrite rel_arr in Hf, Hg; simpl in *.
intros H; apply Hg, Hf, H.
Qed.

Notation "t ; u" := (compose t u) (at level 60).

Lemma compose_id_l : forall {A B} (f : ⊢ A ⊸ B), id; f = f.
Proof.
intros A B [fl fr]; reflexivity.
Qed.

Lemma compose_id_r : forall {A B} (f : ⊢ A ⊸ B), f; id = f.
Proof.
intros A B [fl fr]; reflexivity.
Qed.

Lemma compose_assoc : forall {A B C D} (f : ⊢ A ⊸ B) (g : ⊢ B ⊸ C) (h : ⊢ C ⊸ D),
  f; g; h = f; (g ; h).
Proof.
intros A B C D [fl fr] [gl gr] [hl hr]; reflexivity.
Qed.

(** Tensoriality *)

Definition tns_fun {A B C D} (f : ⊢ A ⊸ B) (g : ⊢ C ⊸ D) : ⊢ A ⊗ C ⊸ B ⊗ D.
Proof.
intros A B C D [fl fr] [gl gr]; split.
+ intros [u v]; split; [apply (fl u)|apply (gl v)].
+ intros [zl zr]; split.
  - intros u; apply gr, zl, fl, u.
  - intros v; apply fr, zr, gl, v.
Defined.

Instance Valid_tns_fun {A B C D} f g : Valid f -> Valid g -> Valid (@tns_fun A B C D f g).
Proof.
intros A B C D [fl fr] [gl gr] [Hf] [Hg]; split.
intros [[u v] [zl zr]].
specialize (Hf (u, zr (gl v))); specialize (Hg (v, zl (fl u))).
rewrite rel_arr in Hf, Hg; simpl in *; tauto.
Qed.

Definition tns_assoc {A B C} : ⊢ A ⊗ B ⊗ C ⊸ A ⊗ (B ⊗ C).
Proof.
intros A B C; split.
+ intros [[u v] w]; simpl; repeat split; assumption.
+ intros [zl zr]; split.
  - intros [u v]; apply zl; assumption.
  - intros w; split.
    { intros u; apply zl; assumption. }
    { intros v; apply zr; split; assumption. }
Defined.

Instance Valid_tns_assoc : forall A B C, Valid (@tns_assoc A B C).
Proof.
intros A B C; split; intros [[[u v] w] [zl zr]]; simpl.
destruct (zl u); tauto.
Qed.

(** *)

Definition lam {A B C} (f : ⊢ A ⊗ B ⊸ C) : ⊢ A ⊸ B ⊸ C.
Proof.
intros A B C [fl fr]; simpl in *; split.
+ intros u; split.
  - intros v; exact (fl (u, v)).
  - intros z; destruct (fr z) as [gl _]; exact (gl u).
+ intros [v z]; destruct (fr z) as [_ gr]; exact (gr v).
Defined.

Instance Valid_lam : forall {A B C} (f : ⊢ A ⊗ B ⊸ C), Valid f -> Valid (lam f).
Proof.
intros A B C [fl fr] [Hf]; split; intros [u [v z]].
specialize (Hf (u, v, z)); rewrite rel_arr in Hf; simpl in *.
destruct (fr z) as [gl gr]; simpl in Hf; tauto.
Qed.

Lemma natural_lam : forall A1 A2 B C (f : ⊢ A1 ⊸ A2) (g : ⊢ A2 ⊗ B ⊸ C),
  extensionality -> f; lam g = lam (tns_fun f id; g).
Proof.
intros A1 A2 B C [fl fr] [gl gr] Hext.
simpl; f_equal.
+ apply Hext; intros u1; f_equal.
  apply Hext; intros z; f_equal.
  destruct (gr z) as [x2 y].
  reflexivity.
+ apply Hext; intros [v z]; f_equal.
  destruct (gr z) as [x2 y].
  reflexivity.
Qed.

Definition eval {A B} : ⊢ (A ⊸ B) ⊗ A ⊸ B.
Proof.
intros A B; split.
+ intros [[fl fr] u]; exact (fl u).
+ intros y; split.
  - intros [fl fr]; exact (fr y).
  - intros u; split; assumption.
Defined.

Instance Valid_eval : forall {A B}, Valid (@eval A B).
Proof.
intros A B; split; intros [[[fl fr] u] y]; simpl.
tauto.
Qed.

(** Cartesian structure *)

Definition prd {A B C} (f : ⊢ C ⊸ A) (g : ⊢ C ⊸ B) : ⊢ C ⊸ A ＆ B.
Proof.
intros A B C [fl fr] [gl gr]; split.
+ intros w; split.
  - apply fl, w.
  - apply gl, w.
+ intros [x|y].
  - apply fr, x.
  - apply gr, y.
Defined.

Instance Valid_prd : forall {A B C} (f : ⊢ C ⊸ A) (g : ⊢ C ⊸ B),
  Valid f -> Valid g -> Valid (prd f g).
Proof.
intros A B C [fl fr] [gl gr] [Hf] [Hg]; split.
intros [z [x|y]]; rewrite rel_arr.
+ specialize (Hf (z, x)); simpl in Hf; tauto.
+ specialize (Hg (z, y)); simpl in Hg; tauto.
Qed.

Definition projl {A B} : ⊢ A ＆ B ⊸ A.
Proof.
intros A B; split.
+ intros [u v]; exact u.
+ intros x; left; assumption.
Defined.

Instance Valid_projl : forall {A B}, Valid (@projl A B).
Proof.
intros A B; split; intros [[u v] x]; simpl; tauto.
Qed.

Definition projr {A B} : ⊢ A ＆ B ⊸ B.
Proof.
intros A B; split.
+ intros [u v]; exact v.
+ intros y; right; assumption.
Defined.

Instance Valid_projr : forall {A B}, Valid (@projr A B).
Proof.
intros A B; split; intros [[u v] x]; simpl; tauto.
Qed.

(** Exponentials *)

(* Definition wth_tns {A B} : ⊢ !(A ＆ B) ⊸ !A ⊗ !B.
Proof.
intros A B; split.
+ intros [u v]; split; assumption.
+ intros [zl zr] [u v].
simpl in u, v.
simpl.
simpl in *.
  specialize (zl u v); specialize (zr v u).
  destruct (rel_decidable _ v zl).
  - left; assumption.
  - right; assumption.
Defined.

Instance Valid_wth_tns {A B} : Valid (@wth_tns A B).
Proof.
intros A B; split; intros [[u v] [zl zr]].
simpl; destruct rel_decidable; simpl; tauto.
Qed.

Definition tns_wth {A B} : ⊢ !A ⊗ !B  ⊸ !(A ＆ B).
Proof.
intros A B; split.
+ intros [u v]; split; assumption.
+ intros f; split; simpl in *.
  - intros u v; destruct (f (u, v)); [apply C_member|assumption].
  - intros u v; destruct (f (v, u)); [assumption|apply C_member].
Defined.

Instance Valid_tns_wth {A B} : Valid (@tns_wth A B).
Proof.
intros A B; split; intros [[u v] z]; simpl; destruct z; simpl; tauto.
Qed.*)

(* Lemma tns_wth_wth_tns_id : forall A B, @tns_wth A B; wth_tns ≅ id.
Proof.
intros A B Hext.
unfold tns_wth, wth_tns, id; simpl; unfold Basics.compose; f_equal.
+ apply Hext; intros [u v]; reflexivity.
+ apply Hext; intros [zl zr]; unfold Datatypes.id; f_equal.
  - apply Hext; intros u; apply Hext; intros v.
    destruct rel_decidable.*)

Definition bng_fun {A B} (f : ⊢ A ⊸ B) : ⊢ !A ⊸ !B.
Proof.
intros A B [fl fr]; split.
+ intros u; apply (fl u).
+ intros z; apply (Rlist.set fl); apply (Rlist.map fr); assumption.
Defined.

Instance Valid_bng_fun {A B} : forall (f :  ⊢ A ⊸ B), Valid f -> Valid (bng_fun f).
Proof.
intros A B [fl fr] [Hf]; split; intros [u y]; apply rel_arr; intros H.
simpl in *.
assert (Hf' := fun u y => Hf (u, y)); simpl in Hf'; clear Hf.
revert y H; refine (
(fix F (y : C (! B)) (H : _) := _
with F_node (n : Rlist.Rnode (W B) (C B)) (H : rel_bng_node rel u (Rlist.set_node fl (Rlist.map_node fr n))) :
  rel_bng_node rel (fl u) n
 := _ for F)).
+ destruct y as [n]; simpl in *; rewrite rel_bng_simpl in *.
  apply F_node, H.
+ destruct n as [|x l].
  - rewrite rel_bng_nil; trivial.
  - simpl in H; rewrite rel_bng_cons in *; split.
   { apply rel_not_not; intros Hc; elim (Hf' u x); intuition. }
   { apply F; intuition. }
Qed.

Lemma compose_bng_fun : forall A B C (f : ⊢ A ⊸ B) (g : ⊢ B ⊸ C),
  bng_fun (f; g) ≅ bng_fun f; bng_fun g.
Proof.
intros A B C [fl fr] [gl gr] Hext; simpl; f_equal.
apply Hext; intros z.
rewrite Rlist.map_set; [|assumption]; rewrite Rlist.set_set; [|assumption].
rewrite Rlist.map_map; [|assumption]; reflexivity.
Qed.

Lemma id_bng_fun : forall A, bng_fun (@id A) ≅ id.
Proof.
intros A Hext; simpl; unfold id; f_equal.
apply Hext; intros z.
rewrite Rlist.map_id; [|assumption].
rewrite Rlist.set_id; [|assumption].
reflexivity.
Qed.

Definition bng_mon {A B} : ⊢ !A ⊗ !B ⊸ !(A ⊗ B).
Proof.
intros A B; split.
+ intros [u v]; split; assumption.
+ intros z; split.
  - intros u.
    exact (Rlist.set (fun (v : W B) => (u, v)) (Rlist.map (fun (p : C (A ⊗ B)) => match p with (fl, _) => fl u end) z)).
  - intros v.
    exact (Rlist.set (fun (u : W A) => (u, v)) (Rlist.map (fun (p : C (A ⊗ B)) => match p with (_, fr) => fr v end) z)).
Defined.

Lemma Valid_bng_mon {A B} : Valid (@bng_mon A B).
Proof.
intros A B; split; intros [[u v] z]; apply rel_arr; intros H; simpl in *.
revert z H; refine (
  fix F (z : C (! (A ⊗ B))) H {struct z} := _
  with F_node (n : Rlist.Rnode _ _) (H : _ n) {struct n} : @rel_bng_node (A ⊗ B) rel (u, v) n := _ for F).
+ destruct z as [n]; simpl in *; rewrite ?rel_bng_simpl in *.
  apply (F_node (n (u, v))).
  pattern (n (u, v)) in H; eexact H.
+ destruct n as [|[xl xr] l]; simpl in *.
  - rewrite rel_bng_nil; trivial.
  - rewrite rel_bng_cons in *; destruct H as [[Hul Hur] [Hvl Hvr]]; split.
    { simpl; split; assumption. }
    { apply F; split; assumption. }
Qed.

Lemma natural_bng_mon : forall A B C D (f : ⊢ A ⊸ C) (g : ⊢ B ⊸ D),
  tns_fun (bng_fun f) (bng_fun g); bng_mon ≅ bng_mon; bng_fun (tns_fun f g).
Proof.
intros A B C D [fl fr] [gl gr] Hext; simpl; f_equal.
+ apply Hext; intros [u v]; reflexivity.
+ apply Hext; intros z; f_equal.
  - apply Hext; intros u.
    rewrite 2 Rlist.map_set; try assumption.
    rewrite 2 Rlist.set_set; try assumption.
    rewrite 2 Rlist.map_map; try assumption.
    repeat f_equal; apply Hext; intros [xl xr]; reflexivity.
  - apply Hext; intros v.
    rewrite 2 Rlist.map_set; try assumption.
    rewrite 2 Rlist.set_set; try assumption.
    rewrite 2 Rlist.map_map; try assumption.
    repeat f_equal; apply Hext; intros [xl xr]; reflexivity.
Qed.

Definition der {A} : ⊢ !A ⊸ A.
Proof.
intros A; split.
+ intros u; exact u.
+ intros x; exact (Rlist.rnode (fun (u : W A) => Rlist.rcons x Rlist.nil)).
Defined.

Instance Valid_der {A} : Valid (@der A).
Proof.
intros A; split; intros [u x]; apply rel_arr; simpl in *.
rewrite rel_bng_simpl, rel_bng_cons; tauto.
Qed.

Lemma natural_der : forall A B (f : ⊢ A ⊸ B),
  der; f ≅ bng_fun f; der.
Proof.
intros A B [fl fr] Hext; simpl; reflexivity.
Qed.

Definition dig {A} : ⊢ !A ⊸ !!A.
Proof.
intros A; split.
+ intros u; exact u.
+ intros x; apply (@Rlist.concat (W A) (C A) x).
Defined.

Instance Valid_dig {A} : Valid (@dig A).
Proof.
intros A; split; intros [u z]; apply rel_arr; intros H; simpl in *.
revert z H.
refine (fix F (z : C (!! A)) H {struct z} := _
  with F_node (n : Rlist.Rnode _ _) (H : _ n) {struct n} : _ n := _ for F).
+ destruct z as [n]; simpl in *.
  rewrite (@rel_bng_simpl (!A)); rewrite rel_bng_simpl in H.
  apply (F_node (n u)); pattern (n u) in H; eexact H.
+ destruct n as [|[n] z]; simpl in *.
  - rewrite rel_bng_nil; trivial.
  - rewrite (@rel_bng_cons (!A)); simpl; rewrite (@rel_bng_simpl).
    destruct (n u) as [|x xz]; clear n; simpl in *.
    { rewrite rel_bng_nil; split; [trivial|].
      destruct z as [n]; simpl in *; rewrite (@rel_bng_simpl !A).
      apply F_node; assumption. }
    { rewrite rel_bng_cons in *.
      destruct H as [Hux H].
      apply rel_bng_app in H.
      intuition. }
Qed.

Lemma natural_dig : forall A B (f : ⊢ A ⊸ B),
  dig; bng_fun (bng_fun f) ≅ bng_fun f; dig.
Proof.
intros A B [fl fr] Hext; simpl; f_equal.
apply Hext; intros z.
rewrite Rlist.map_concat; [|assumption].
rewrite Rlist.set_concat; [|assumption].
repeat f_equal.
rewrite <- Rlist.map_map; [|assumption].
reflexivity.
Qed.

Lemma dig_der_id_1 : forall A, @dig A; der ≅ id.
Proof.
intros A Hext; unfold dig, der, id; simpl; f_equal.
apply Hext; intros [n]; unfold Datatypes.id; simpl.
f_equal; apply Hext; intros u.
Qed.

Lemma dig_der_id_2 : forall A, @dig A; bng_fun der ≅ id.
Proof.
intros A Hext; unfold dig, der, id; simpl; f_equal.
apply Hext; intros z; apply Hext; intros u.
rewrite List.map_map.
unfold Datatypes.id; set (Z := z u) in *; clearbody Z; clear z.
induction Z as [|x z IH]; simpl.
+ reflexivity.
+ rewrite IH; reflexivity.
Qed.

Lemma dig_assoc : forall A, @dig A; dig ≅ dig; bng_fun dig.
Proof.
intros A Hext; unfold dig; simpl; f_equal.
apply Hext; intros z; apply Hext; intros u; repeat f_equal.
set (Z := z u); clearbody Z; clear z; induction Z as [|x z IH].
+ reflexivity.
+ simpl; rewrite IH; clear IH.
  induction z as [|y z IHz]; simpl.
  - rewrite List.app_nil_r.
Admitted.

Lemma der_mon : forall A B, @bng_mon A B; der ≅ tns_fun der der.
Proof.
intros A B Hext; simpl; f_equal.
apply Hext; intros [fl fr]; f_equal.
Qed.

Lemma dig_mon : forall A B, @bng_mon A B; dig ≅ tns_fun dig dig; bng_mon; bng_fun bng_mon.
Proof.
intros A B Hext; simpl; f_equal.
+ apply Hext; intros [u v]; reflexivity.
+ apply Hext; intros z; f_equal.
  - apply Hext; intros u; apply Hext; intros v.
    rewrite List.concat_map; rewrite ?List.map_map; reflexivity.
  - apply Hext; intros u; apply Hext; intros v.
    rewrite List.concat_map; rewrite ?List.map_map; reflexivity.
Qed.

Definition dup {A} : ⊢ !A ⊸ !A ⊗ !A.
Proof.
intros A; split.
+ intros u; split; exact u.
+ intros [xl xr] u.
  (** There is a choice here... *)
  specialize (xl u u); specialize (xr u u).
  exact (xl ++ xr)%list.
Defined.

(* Definition dup' {A} : ⊢ !A ⊸ !A ⊗ !A.
Proof.
intros A; split.
+ intros u; split; exact u.
+ intros [xl xr] u.
  induction A; simpl in *.
  admit.
  
  (** There is a choice here... *)
  specialize (xl u u); specialize (xr u u).
  destruct (rel_decidable _ u xl); [|exact xl].
  destruct (rel_decidable _ u xr); [|exact xr].
  apply C_member.
Defined. *)

Instance Valid_dup {A} : Valid (@dup A).
Proof.
intros A; split; intros [u [xl xr]]; apply rel_arr; intros H.
simpl in *.
set (X := xl u u) in *; set (Y := xr u u) in *; clearbody X Y; clear xl xr.
induction X as [|x xl IH]; simpl in *; intuition.
Qed.

Lemma dup_coalg : forall A, @dig A; bng_fun dup ≅ dup; tns_fun dig dig; bng_mon.
Proof.
intros A Hext; simpl; f_equal.
apply Hext; intros z; apply Hext; intros u.
rewrite ?List.map_map.
set (Z := z (u, u)); clearbody Z; clear z.
induction Z as [|[xl xr] z IH]; simpl.
+ reflexivity.
+ rewrite IH; f_equal.
Qed.

Lemma dig_comon : forall A, @dig A; dup ≅ dup; tns_fun dig dig.
Proof.
intros A Hext; simpl; f_equal.
apply Hext; intros [zl zr]; apply Hext; intros u; simpl.
repeat destruct rel_decidable; f_equal; simpl in *; tauto.
Qed.

Let dup_mon_comm {A B C D} : ⊢ (!A ⊗ !B) ⊗ (!C ⊗ !D) ⊸ (!A ⊗ !C) ⊗ (!B ⊗ !D).
Proof.
intros A B; split; simpl.
+ intros [[a b] [c d]]; repeat split; assumption.
+ intros [zl zr]; split.
  - intros [a b]; split; [intros c d; apply zl|intros d c; apply zr]; repeat split; auto.
  - intros [c d]; split; [intros a b; apply zl|intros b a; apply zr]; repeat split; auto.
Defined.

(* Lemma dup_mon : forall A B,
  @bng_mon A B; dup ≅ tns_fun dup dup; dup_mon_comm; tns_fun bng_mon bng_mon.
Proof.
intros A B Hext; simpl; f_equal.
+ apply Hext; intros [u v]; reflexivity.
+ apply Hext; intros [zl zr]; f_equal.
  - apply Hext; intros u; apply Hext; intros v.
    repeat destruct rel_decidable; destruct (zl (u, v) (u, v)), (zr (u, v) (u, v)); try tauto.
*)


(*Lemma natural_dup : forall A B (f : ⊢ A ⊸ B), Valid f ->
  bng_fun f; dup ≅ dup; tns_fun (bng_fun f) (bng_fun f).
Proof.
intros A B [fl fr] [Hf] Hext; f_equal; simpl; f_equal.
apply Hext; intros [zl zr]; apply Hext; intros u; simpl in *.
assert (Hfl := Hf (u, zl (fl u) (fl u))).
assert (Hfr := Hf (u, zr (fl u) (fl u))).
simpl in Hfl, Hfr.
repeat destruct rel_decidable; f_equal; try tauto.
2: exfalso; specialize (Hf (u, zl (fl u) (fl u))); simpl in Hf; exfalso; tauto.
exfalso.
specialize (Hf (u, zl (fl u) (fl u))).
 simpl in Hf.

Qed.*)

Definition undual {A} : ⊢ ((A ⊸ [false]) ⊸ [false]) ⊸ A.
Proof.
intros A; split.
+ intros [f g].
  apply g; apply daimon.
+ intros x; split.
  - split; [intros; constructor|intros; assumption].
  - apply daimon.
Defined.

Instance Valid_undual {A} : Valid (@undual A).
Proof.
intros A; split; intros [[fl fr] x]; simpl.
destruct (fr daimon); simpl.
tauto.
Qed.

Definition wkn {A} : ⊢ A ⊸ [true].
Proof.
intros A; split.
+ intros _; constructor.
+ intros _; apply C_member.
Defined.

(* Lemma natural_wkn : forall A B (f : ⊢ A ⊸ B), Valid f -> bng_fun f; wkn ≅ wkn.
Proof.
intros A B [fl fr] [Hf] Hext; unfold wkn; simpl; f_equal.
apply Hext; intros []; apply Hext; intros u. *)

(* Lemma toto : forall A, W A -> C A.
Proof.
intros A; induction A.
+ intros []; constructor.
+ admit.
+ intros [u v]; split.
  intros w.
  apply IHA2.
  admit.
  admit.
+ intros u u'.
  admit.
+ simpl.
  admit.
+ intros f.
  simpl in *.*)


(* Instance Valid_wkn : forall A, Valid (@wkn A).
Proof.
intros A; split; intros [u []]; simpl.
tauto.
Qed. *)

Definition absurd {A} : ⊢ [false] ⊸ A.
Proof.
intros A; split.
+ intros []; apply W_member.
+ intros _; apply C_member.
Defined.

Instance Valid_absurd : forall A, Valid (@absurd A).
Proof.
intros A; split; intros [[] x]; simpl; tauto.
Qed.

Definition forall_intro {T : Inhabited} (A : prp) (B : T -> prp) :
  (forall x : T, ⊢ A ⊸ B x) -> ⊢ A ⊸ ∀ x : T, B x.
Proof.
intros T A B p; split.
+ intros u t; specialize (p t); exact (app p u).
+ intros [t y]; destruct (p t) as [_ q]; apply (q y).
Defined.

Instance Valid_forall_intro :
  forall T A B f, (forall t, Valid (f t)) -> Valid (@forall_intro T A B f).
Proof.
intros T A B f Hf; split.
intros [u [t y]]; simpl.
specialize (Hf t); destruct (f t); destruct Hf as [Hf].
exact (Hf (u, y)).
Qed.

Definition forall_elim {T : Inhabited} (t : T) (A : T -> prp) : ⊢ (∀ t : T, A t) ⊸ A t.
Proof.
intros T t A; split.
+ intros f; apply (f t).
+ intros x; simpl; exists t; exact x.
Defined.

Instance Valid_forall_elim : forall T t A, Valid (@forall_elim T t A).
Proof.
intros T t A; split.
intros [u y]; simpl; tauto.
Qed.

Definition exists_intro {T : Inhabited} (t : T) (A : T -> prp) : ⊢ A t ⊸ ∃ x : T, A x.
Proof.
intros T t A; split.
+ intros u; exists t; exact u.
+ intros f; specialize (f t); exact f.
Defined.

Instance Valid_exists_intro : forall T t A, Valid (@exists_intro T t A).
Proof.
intros T t A; split.
intros [u z]; simpl; tauto.
Qed.

(** This is the rule in which we need the dependency of counters in existential statements. *)

Definition exists_elim (T : Inhabited) (A : prp) (B : T -> prp)
  (f : forall x : T, ⊢ B x ⊸ A) : ⊢ (∃ x : T, B x) ⊸ A.
Proof.
intros T A B f; split.
+ intros [t u]; specialize (f t).
  destruct f as [f _]; exact (f u).
+ intros x t; specialize (f t).
  destruct f as [_ f]; exact (f x).
Defined.

Instance Valid_exists_elim : forall T A B f,
  (forall x, Valid (f x)) -> Valid (@exists_elim T A B f).
Proof.
intros T A B f Hf; split.
intros [[t v] x]; apply rel_arr; intros H; simpl.
specialize (Hf t); destruct Hf as [Hf].
specialize (Hf (v, x)); simpl in *.
destruct (f t) as [fl fr]; apply rel_not_not; tauto.
Qed.

Lemma exists_id : forall (T : Inhabited) (A : T -> prp) (B : prp) (t : T)
  (f : forall t : T, ⊢ A t ⊸ B),
  @exists_intro T t A; @exists_elim T B A f ≅ (f t).
Proof.
intros T A B t f Hext; simpl.
destruct (f t) as [fl fr]; f_equal.
Qed.

Definition Exists_elim (T : Inhabited) (A : prp) (B : T -> prp)
  (f : forall x : T, ⊢ !(B x) ⊸ A) : ⊢ (∃ x : T, !(B x)) ⊸ A.
Proof.
intros T A B f; split.
+ intros [t u]; specialize (f t).
  destruct f as [f _]; apply (f u).
+ intros x t u; specialize (f t).
  destruct f as [_ f].
  apply (f x u).
Defined.

Instance Valid_Exists_elim : forall T A B f,
  (forall x, Valid (f x)) -> Valid (@Exists_elim T A B f).
Proof.
intros T A B f Hf; split.
intros [[t w] x]; apply rel_arr; intros Hw; simpl in *.
specialize (Hf t); destruct Hf as [Hf]; specialize (Hf (w, x)).
destruct (f t); simpl in *.
apply rel_not_not; tauto.
Qed.

(* Definition gapp {Γ A B} (t : ⊢ !Γ ⊸ !A ⊸ B) (u : ⊢ !Γ ⊸ A) : ⊢ !Γ ⊗ !Γ ⊸ B :=
  tns_fun t (dig; bng_fun u); eval.

Lemma rw : forall Γ A B t u, snd (@gapp Γ A B t u) ≅
  fun k => (
    (fun x1 x2 => snd u (snd (fst t x1) k (fst u x2)) x2),
    (fun x => snd t (fst u x, k))).
Proof.
intros Γ A B t u Hext; fold C W; unfold gapp, tns_fun, bng_fun; simpl; apply Hext.
intros k; destruct u as [ul ur]; destruct t as [tl tr]; simpl.
f_equal; apply Hext.
intros e1; apply Hext.
intros e2; destruct (tl e1); reflexivity.
Qed.

Eval compute -[C W C_member] in fun A B u => .

Lemma toto : forall A, {Valid (W_member A)} + {Valid

Definition t := Eval compute -[C W C_member] in fun Γ A B t u => snd (@gapp Γ A B t u).
Extraction t.
Eval compute in (snd t).

Definition gapp {Γ A B} (t : ⊢ !Γ ⊸ !A ⊸ B) (u : ⊢ !Γ ⊸ A) : ⊢ !Γ ⊸ B.
Proof.
intros Γ A B [tl tr] [ul ur]; split; simpl in *.
+ intros w; specialize (tl w); destruct tl as [tl _].
  apply tl, ul, w.
+ intros y w.
  specialize (tl w); destruct tl as [_ tl].
  specialize (ul w); specialize (tl y ul).
  specialize (tr (ul, y) w).
  specialize (ur tl w).
  destruct (rel_decidable Γ w tr).
  - apply ur.
  - apply tr.
Defined.

Lemma Valid_gapp : forall Γ A B t u, Valid (@gapp Γ A B t u).
Proof.
intros Γ A B [tl tr] [ul ur]; split.
intros [w y]; apply rel_arr; simpl; intros Hr.
remember (tl w) as f.
destruct f as [fl fr].
destruct rel_decidable.
+ admit.
+ contradiction.*)

