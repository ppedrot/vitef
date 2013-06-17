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

Require Import Bool Morphisms Setoid.

Definition extensionality := forall A (B : A -> Type) (f g : forall x, B x),
  (forall x : A, f x = g x) -> f = g.

Definition ext_eq {A} (x y : A) := extensionality -> x = y.

Notation "x ≅ y" := (ext_eq x y) (at level 70).

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
     | bng p => W p -> C p
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

Fixpoint rel (A : prp) : W A -> C A -> Prop :=
  match A return W A -> C A -> Prop with
    | atm p => (fun _ _ => Is_true p)
    | pls A B => rel_pls rel
    | tns A B => rel_tns rel
    | bng A => fun u y => rel A u (y u)
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
+ apply IHA.
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

(** The types [W] and [C] are always inhabited because we restrict quantifiers to inhabited
   types. *)

Definition WC_member (A : prp) : W A * C A.
Proof.
  induction A; unfold W; unfold C; simpl; fold W; fold C; split; try firstorder.
  apply daimon.
  exact (member T).
Defined.
 
Definition W_member (A : prp) := fst (WC_member A).
Definition C_member (A : prp) := snd (WC_member A).

(** The predicate [valid p] is the Dialectica interpretation of [p]. It says that there is
   [w] such that [rel p w c] holds for any [c]. In terms of games semantics this means
   that [W] has a winning strategy (which amounts to a winning move [w]). *)

Notation "⊢ A" := (W A) (at level 89).
Notation "⊣ A" := (C A) (at level 89).

Class Valid {A} (f : ⊢ A) := { valid_spec : forall b : C A, rel A f b }.

CoInductive ValidI {A} (f : ⊢ A) := validI : ValidI f -> ValidI f.

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

Definition wth_tns {A B} : ⊢ !(A ＆ B) ⊸ !A ⊗ !B.
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
Qed.

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
+ intros y u.
  apply fr, y, fl, u.
Defined.

Instance Valid_bng_fun {A B} : forall (f :  ⊢ A ⊸ B), Valid f -> Valid (bng_fun f).
Proof.
intros A B [fl fr] [Hf]; split; intros [u y]; simpl in *.
specialize (Hf (u, (y (fl u)))); simpl in *; assumption.
Qed.

Lemma compose_bng_fun : forall A B C (f : ⊢ A ⊸ B) (g : ⊢ B ⊸ C),
  bng_fun (f; g) = bng_fun f; bng_fun g.
Proof.
intros A B C [fl fr] [gl gr]; reflexivity.
Qed.

Lemma id_bng_fun : forall A, bng_fun (@id A) = id.
Proof.
intros A; reflexivity.
Qed.

Definition bng_mon {A B} : ⊢ !A ⊗ !B ⊸ !(A ⊗ B).
Proof.
intros A B; split.
+ intros [u v]; split; assumption.
+ intros z; split.
  - intros u v; destruct (z (u, v)) as [f _]; exact (f u).
  - intros v u; destruct (z (u, v)) as [_ f]; exact (f v).
Defined.

Lemma Valid_bng_mon {A B} : Valid (@bng_mon A B).
Proof.
intros A B; split; intros [[u v] z]; apply rel_arr; simpl in *.
destruct (z (u, v)); simpl; tauto.
Qed.

Lemma natural_bng_mon : forall A B C D (f : ⊢ A ⊸ C) (g : ⊢ B ⊸ D),
  tns_fun (bng_fun f) (bng_fun g); bng_mon ≅ bng_mon; bng_fun (tns_fun f g).
Proof.
intros A B C D [fl fr] [gl gr] Hext; simpl; f_equal.
+ apply Hext; intros [u v]; reflexivity.
+ apply Hext; intros z; f_equal.
  - apply Hext; intros u; apply Hext; intros v.
    destruct z; reflexivity.
  - apply Hext; intros v; apply Hext; intros u.
    destruct z; reflexivity.
Qed.

Definition der {A} : ⊢ !A ⊸ A.
Proof.
intros A; split.
+ intros u; exact u.
+ intros u _; exact u.
Defined.

Instance Valid_der {A} : Valid (@der A).
Proof.
intros A; split; intros [u x]; apply rel_arr; simpl in *; tauto.
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
+ intros x u; exact (x u u).
Defined.

Instance Valid_dig {A} : Valid (@dig A).
Proof.
intros A; split; intros [u x]; simpl in *; tauto.
Qed.

Lemma natural_dig : forall A B (f : ⊢ A ⊸ B),
  dig; bng_fun (bng_fun f) ≅ bng_fun f; dig.
Proof.
intros A B [fl fr] Hext; simpl; reflexivity.
Qed.

Lemma dig_der_id_1 : forall A, @dig A; der ≅ id.
Proof.
intros A Hext; unfold dig, der, id; simpl; f_equal.
Qed.

Lemma dig_der_id_2 : forall A, @dig A; bng_fun der ≅ id.
Proof.
intros A Hext; unfold dig, der, id; simpl; f_equal.
Qed.

Lemma dig_assoc : forall A, @dig A; dig ≅ dig; bng_fun dig.
Proof.
intros A Hext; unfold dig; simpl; f_equal.
Qed.

Lemma der_mon : forall A B, @bng_mon A B; der ≅ tns_fun der der.
Proof.
intros A B Hext; simpl; f_equal.
apply Hext; intros [fl fr]; f_equal.
Qed.

Lemma dig_mon : forall A B, @bng_mon A B; dig ≅ tns_fun dig dig; bng_mon; bng_fun bng_mon.
Proof.
intros A B Hext; simpl; f_equal.
apply Hext; intros [u v]; reflexivity.
Qed.

Definition dup {A} : ⊢ !A ⊸ !A ⊗ !A.
Proof.
intros A; split.
+ intros u; split; exact u.
+ intros [xl xr] u.
  (** There is a choice here... *)
  specialize (xl u u); specialize (xr u u).
  destruct (rel_decidable _ u xl); [|exact xl].
  destruct (rel_decidable _ u xr); [|exact xr].
  apply C_member.
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
intros A; split; intros [u [xl xr]] H; simpl in *.
repeat destruct rel_decidable; tauto.
Qed.

Lemma dup_coalg : forall A, @dig A; bng_fun dup ≅ dup; tns_fun dig dig; bng_mon.
Proof.
intros A Hext; simpl; f_equal.
apply Hext; intros z; apply Hext; intros u.
destruct (z (u, u)); reflexivity.
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

Definition WKN {A} : (W A -> C A).
Proof.
induction A; simpl.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
Admitted.

Definition wkn {A} : ⊢ !A ⊸ [true].
Proof.
intros A; split.
+ intros _; constructor.
+ intros ctx u.
Admitted.

Let par A B := opp (tns (opp A) (opp B)).
Eval simpl in fun A B => W (par (whn A) (whn B)).

Definition wkn' {A} : ⊢ A ⊸ [true].
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

Definition markov {A} : ⊢ (!?! A) ⊸ A.
Proof.
intros A; split; simpl.
+ intros f; apply f; intros _; apply C_member.
+ intros x f u; exact x.
Defined.

Lemma Valid_markov : forall A, Valid (@markov A).
Proof.
intros A; split; unfold markov; intros [u x]; apply rel_arr; simpl.
intros Hr; apply rel_not_not in Hr.




Definition em {A B} : ⊢ ?(A ⊕ (A ⊸ ? B)).
Proof.
intros A B [x [u y]]; simpl in *.
destruct (rel_decidable A u x).
+ left; assumption.
+ right; split.
  - intros; apply W_member.
  - intros; assumption.
Defined.

Definition toto {A B} : ⊢ ? A ⊕ ? B ⊸ ? (A ⊕ B).
Proof.
intros A B; split.
+ intros [u|v] [kl kr]; simpl in *.
  - left; apply u, kl.
  - right; apply v, kr.
+ intros [x y]; split; assumption.
Defined.

Lemma Valid_em : forall A B, Valid (@em A B).
Proof.
intros A B; split.
intros [x [u y]]; simpl; intros Hc; apply Hc; clear Hc.
destruct rel_decidable as [Hd|Hd]; simpl.
+ assumption.
+ intros [Hc _]; contradiction.
Qed.

Definition callcc {A B} : ⊢ !(!(!A ⊸ ?! B) ⊸ ?! A) ⊸ ?! A.
Proof.
intros A B; split.
+ intros [fl fr] π.
  simpl in *; apply fl; [|exact π]; split.
  - intros; apply W_member.
  - intro; exact π.
+ intros f [kl kr]; split.
  - simpl; split.
    { intros; apply W_member. }
    { intro; exact f. }
  - exact f.
Defined.

Lemma rel_not_not_stable : forall A u x, ~~ (rel A u x) <-> rel A u x.
Proof.
intros A u x; split; [apply rel_not_not|intuition].
Qed.

Lemma Valid_callcc : forall A B, Valid (@callcc A B).
Proof.
intros A B; exists.
intros [[ul ur] π]; apply rel_arr; intros Hu.
simpl in *.
destruct ur as [u ρ].
simpl in *.
repeat rewrite rel_not_not_stable in *.
(* Definition markov {P} : ⊢ ?!? P ⊸ P.
Proof.
intros P f; split; simpl in *.
+ intros w; apply f.
  admit.
+ intros f; apply f.
  apply C_member.
+ intros x; exact x.
Defined.*)

(* Instance Valid_markov : forall P, Valid (@markov P).
Proof.
intros P; split; intros [w x]; apply rel_arr; intros Hw; simpl in *.
assumption.
Qed. *)

(* Definition markov_nat (T : Inhabited) (P : T -> prp) :
  ⊢ ! (¬ (∀ x : T, ¬ (P x))) ⊸ ∃ x : T, !(P x).
Proof.
intros T P; split.
+ intros; simpl in *; apply H.
  intros x u; apply C_member.
+ simpl; intros w f t u.
  apply (w _ u).
Defined.*)

Inductive pos : prp -> Type :=
| pos_one : pos [true]
| pos_nul : pos [false]
| pos_tns : forall A B, pos A -> pos B -> pos (A ⊗ B)
| pos_sum : forall A B, pos A -> pos B -> pos (A ⊕ B).

Lemma dup_pos : forall A, pos A -> ⊢ A ⊸ A ⊗ A.
Proof.
intros A HA; induction HA as [| |A B HA IHA HB IHB|A B HA IHA HB IHB];
  (split; [intros u|intros [zl zr]]).
+ repeat constructor.
+ apply daimon.
+ repeat constructor.
+ apply daimon.
+ destruct u as [u v]; repeat split; assumption.
+ split.
  - intros u. admit.
  - admit.
  
+ admit.
+ simpl. admit.
Admitted.

Definition search (p : N -> prp) (m : N) :
  W (p 0) ->
  (forall k : N, W (p k) -> W (p (S k))) ->
  (forall k : N, W (p k) -> C (p k)) ->
  C (p m) ->
  C (p 0) + {n : N & (W (p n) * C (p (S n)))%type}.
Proof.
  intros p m z s b c.
  induction m.
  left; exact c.
  pose (w := nat_rect _ z s m).
  destruct (rel_decidable (p m) w (b m (w))) as [D1|D2].
  right.
  exists m.
  exact (w, c).
  apply IHm.
  exact (b m (w)).
Defined.

Eval simpl in fun A B => ⊣ par A B.
Eval simpl in fun A B (w : ⊢ par A B) (z : ⊣ par A B) => rel (par A B) w z.

(* Definition Nrec {P} : ⊢ !(P 0) ⊗ !(∀ n : N, !(P n) ⊸ P (S n)) ⊸ (∀ m : N, P m).
Proof.
intros P; split.
+ intros [H0 HS] m; induction m.
  - exact H0.
  - apply HS; assumption.
+ simpl; intros [m Hm].
  induction m as [|m]; split.
  - intros u.

split.
  intros H0 HS.
  apply 
  Print search.
  Extraction search.
+ intros [m Hm]; induction m as [|m]; split.
  - intros H0 f; specialize (f 0); destruct f as [fl fr].
    
    exists 0; split; auto.
  - intros H0 f; simpl.
    exists m; split.
    { clear - H0 f; induction m; [assumption|apply f, IHm]. }
    { specialize (f m); destruct f as [_ f].
    *)
(** * Equality

   Next we verify the rules of equality. To keep things simple we only consider equality
   of natural numbers. In the general case we could consider decidable equality on an
   inhabited type. *)

(*

Definition prpEq (m n : N) := [beq_nat m n].

(** Dialectica equality implies equality. *)

Theorem prpEq_eq (m n : N) (p : ⊢ prpEq m n) : Valid p -> m = n.
Proof.
intros m n p [Hp].
specialize (Hp daimon); simpl in Hp.
apply beq_nat_true.
apply Is_true_eq_true.
assumption.
Qed.

(** Equality implies Dialectica equality, of course, but notice how complicated the proofs
   seems to be. We could move the complication into [prpEq_refl] below. *)

Definition eq_prpEq (m n : N) : ⊢ prpEq m n.
Proof.
intros m n; exact tt.
Defined.

Instance Valid_eq_prpEq : forall m n, m = n -> Valid (eq_prpEq m n).
Proof.
intros m n Heq; split; intros x; simpl.
apply Is_true_eq_left.
apply beq_nat_true_iff; assumption.
Qed.

(** Reflexivity. *)

Theorem prpEq_refl (n : N) : Valid (eq_prpEq n n).
Proof.
  intros n; split.
  intros x; simpl.
  rewrite <- beq_nat_refl; constructor.
Qed.

(** Leibniz's law as a rule of inference. *)

Definition Leibniz {P : N -> prp} {m n : N} (e : ⊢ prpEq m n) (p : ⊢ P m) : ⊢ P n.
Proof.
intros P m n [].

Theorem leibniz_rule (p : N -> prp) (m n : N) :
  valid (prpEq m n) -> valid (p m) -> valid (p n).
Proof.
  unfold valid, C, W; simpl; fold C; fold W.
  intros p m n [a H] [b G].
  assert (E := H tt).
  apply Is_true_eq_true in E.
  apply beq_nat_true in E.
  rewrite <- E.
  exists b.
  assumption.
Qed.

(** Proving Leibniz's law as a proposition is more complicated because of type dependency
   that is not present in the usual Dialectica interpretation.

   In fact, it looks like we need UIP (Uniqueness of Identity Proofs) for natural numbers,
   which luckily holds since the natural numbers are decidable. Below we prove UIP for N.
   Coq 8.3 contains a more general proof of UIP for decidable types, see [Logic.Eqdep_dec]. *)

Definition eqN_compose (k m n : N) (p : k = m) (q : k = n) : m = n.
Proof.
  intros k m n p q.
  induction p.
  exact q.
Defined.

Lemma eqN_compose_transitivity (m n : N) (p : m = n) : eqN_compose p p = refl_equal n.
Proof.
  intros m n p.
  case p; trivial.
Qed.

Lemma eqN_decidable (m n : N) : {m = n} + {m <> n}.
Proof.
  induction m; induction n; auto.
  destruct (IHm n) as [E1 | E2].
  rewrite E1.
  left.
  reflexivity.
  right.
  injection.
  contradiction.
Qed.

Definition eqN_nu (m n : N) (p : m = n) : (m = n).
Proof.
  intros m n p.
  destruct (eqN_decidable m n) as [EQ|NEQ].
  exact EQ.
  contradiction.
Defined.

Definition eqN_mu (m n : N) (p : m = n) := eqN_compose (eqN_nu (refl_equal m)) p.

Lemma eqN_mu_nu (n m : N) (p : n = m) : eqN_mu (eqN_nu p) = p.
Proof.
  intros n m p.
  case p.
  unfold eqN_mu.
  apply eqN_compose_transitivity.
Qed.

Theorem UIP_N : forall (m n : N) (p q : m = n), p = q.
Proof.
  intros m n p q.
  elim eqN_mu_nu with (p := p).
  elim eqN_mu_nu with (p := q).
  unfold eqN_nu.
  destruct (eqN_decidable m n) as [EQ|NEQ].
  reflexivity.
  contradiction.
Qed.

Definition W_transfer (p : N -> prp) (m n : N) : W (p m) -> W (p n).
Proof.
  intros p m n w.
  destruct (eqN_decidable m n) as [E1 | E2].
  rewrite <- E1.
  exact w.
  exact (W_member ((p n))).
Defined.

Definition C_transfer (p : N -> prp) (m n : N) : C (p m) -> C (p n).
Proof.
  intros p m n c.
  destruct (eqN_decidable m n) as [E1 | E2].
  rewrite <- E1.
  exact c.
  exact (C_member ((p n))).
Defined.

(** Finally, the validity of Leibniz's law is proved. If someone knows a shortcut,
   I would like to know about it. *)

Theorem leibniz (p : N -> prp) (m n : N) : valid (prpEq m n ==> p m ==> p n).
Proof.
  intros p m n.
  unfold valid, C, W; simpl; fold C; fold W.
  exists ((fun tt => ((fun (w : W (p m)) => W_transfer p m n w),
                      (fun y => C_transfer p n m (snd y)))),
          (fun _ => tt)).
  intros [u [w c]].
  simpl.
  intros E.
  apply Is_true_eq_true in E.
  apply beq_nat_true in E.
  destruct E.
  unfold C_transfer, W_transfer.
  destruct (eqN_decidable m m) as [E1 | E2].
  assert (U := UIP_N E1 (refl_equal m)).
  rewrite U.
  simpl.
  auto.
  assert (F2 : m = m); auto.
  contradiction.
Qed.

(** * Natural numbers

   Next we verify that the natural numbers obey Peano axioms. They are easy, except for
   induction which has two parts: the usual "forward" direction by primitive recursion,
   and a "backwards" direction in which we search for a counter-example, starting from an
   upper bound and going down to 0. *)

Theorem nat_zero_not_succ (n : nat) :
  valid (neg (prpEq (S n) 0)).
Proof.
  intro n.
  unfold valid, C, W; simpl; fold C; fold W.
  exists (fun tt => tt); auto.
Qed.

Theorem succ_injective (m n : nat) :
  valid (prpEq (S m) (S n) ==> prpEq m n).
Proof.  
  intros m n.
  unfold valid, C, W; simpl; fold C; fold W.
  exists (fun _ => tt, fun _ => tt); auto.
Qed.

(** Given a propositional function [p : nat -> prp], suppose [p m] is not valid. Then [p
   0] is not valid, or one of induction steps [p k ==> p (S k)] fails. The "backwards"
   direction of the Dialectica interpretation of induction is a search functional which
   looks for a failed base case or failed induction step. We construct it separately from
   the main proof. *)

Definition search (p : N -> prp) (m : N) :
  W (p 0) ->
  (forall k : N, W (p k) -> W (p (S k))) ->
  (forall k : N, W (p k) * C (p (S k)) -> C (p k)) ->
  C (p m) ->
  C (p 0) + {n : N & (W (p n) * C (p (S n)))%type}.
Proof.
  intros p m z s b c.
  induction m.
  left; exact c.
  pose (w := nat_rect _ z s m).
  destruct (rel_decidable (p m) w (b m (w, c))) as [D1|D2].
  right.
  exists m.
  exact (w, c).
  apply IHm.
  exact (b m (w, c)).
Defined.

(** Finally we verify validity of induction. *)

Theorem N_induction (p : nat -> prp) (m : nat) :
  valid (p 0 and (all n : N, p n ==> p (S n)) ==> p m).
Proof.
  intros p m.
  unfold valid, C, W; simpl; fold C; fold W.
  exists (fun x => nat_rect _ (fst x) (fun k => fst (snd x k)) m,
          fun y => search p m (fst (fst y))
                     (fun k => fst (snd (fst y) k))
                     (fun k => snd (snd (fst y) k))
                     (snd y)).
  simpl.
  intros [[z h] c]; simpl.
  set (s := fun k : nat => fst (h k)).
  set (b := fun k : nat => snd (h k)).
  induction m; auto.
  unfold search; simpl.
  set (w := nat_rect (fun k : nat => W (p k)) z s m).
  destruct (rel_decidable (p m) w (b m (w, c))) as [D1|D2]; simpl.
  intro H.
  apply H.
  apply D1.
  intros.
  assert (G:= IHm (b m (w, c))).
  fold w in G.
  elim D2.
  apply G.
  apply H.
Qed.
*)
(** Having done ordinary induction one is tempted to try validating induction for
   W-types... but not here. *)

(** * Markov Principle and Independence of Premise *)

(** The Dialectica interpretation is characterized by two non-intuitionistic reasoning principles,
   namely Markov principle (MP) and Independence of Premise (IP).

   Both MP and IP involve primitive propositional function [N -> bool]. The point of
   these is that their [W] and [C] types are the unit. So instead of actually using
   primitive proposition, we shall use arbitrary propositions whose [W] and [C] types are
   singletons. First we make the relevant definitions. *)

Definition singleton (t : Inhabited) := forall x, x = member t.

Definition trivial_C (p : prp) := singleton (inhabit (C_member p)).
Definition trivial_W (p : prp) := singleton (inhabit (W_member p)).

(** Primitive propositions are trivial, of course. *)

Lemma primitive_trivial_W (b : bool) : trivial_W ([b]).
Proof.
  intros b w.
  case w; auto.
Qed.

Lemma primitive_trivial_C (b : bool) : trivial_C ([b]).
Proof.
  intros b c.
Admitted.

(** Whether there are trivial propositions, other than the primitive ones, depends on what
   extra axioms we have available. For example, in the presence of extensionality of
   functions, implications and negations of trivial propositions are trivial. We do not
   dwell on the exact conditions that give us trivial propositions, but only demonstrate
   how to use extensionality of functions whose codomain is a singleton set to derive
   triviality of implication of trivial propositions.
*)

(** Is there a better way of getting the next lemma? *)

Lemma pair_equal (X Y : Type) (p q : X * Y) :
  fst p = fst q -> snd p = snd q -> p = q.
Proof.
  intros X Y p q G H.
  induction p; induction q.
  simpl in G; simpl in H.
  rewrite G; rewrite H.
  reflexivity.
Qed.

(** We are only interested in extensionality of functions [s -> t] for which
   [t] is a singleton. Such extensionality can be phrased as "any power of a
   singleton is a singleton". *)

Definition singleton_power :=
  forall t, singleton t -> forall s : Type, singleton (inhabit (fun _ : s => member t)).

(** I _think_ there is no way of proving [singleton_power], is there? We can use it to
   show that [W (p ==> q)] is trivial if [C p] and [W q] are trivial. *)

Lemma implication_trivial_W (p q : prp) :
  singleton_power -> trivial_C p -> trivial_W q -> trivial_W (p ⊸ q).
Proof.
  intros p q E TCp TWq.
  unfold trivial_W.
  unfold singleton.
  unfold W_member, C_member; simpl; fold W_member; fold C_member.
  intros [f g].
  apply pair_equal; simpl.
  rewrite (E _ TWq _).
  rewrite (E _ TWq _ f).
  reflexivity.
  rewrite (E _ TCp _).
  rewrite (E _ TCp _ g).
  reflexivity.
Qed.

(** Triviality of [C (p ==> q)] does not require any extra assumptions. *)
Lemma implication_trivial_C (p q : prp) :
  trivial_W p -> trivial_C q -> trivial_C (p ⊸ q).
Proof.
  intros p q TWp TCq.
  unfold trivial_C.
  unfold C, W; simpl; fold C; fold W.
  intros [wp cq].
  rewrite (TWp wp).
  rewrite (TCq cq).
  apply pair_equal; auto.
Qed.

(** ** Markov principle *)
  
(** Markov principle holds for any inhabited type (not just the natural numbers) and
   a proposition which has trivial [W] and [C] types. *)

Theorem markov_generalized (T : Inhabited) (P : T -> prp) :
  ⊢ ! (neg (∀ t : T, neg (P t))) ⊸ ∃ t : T, ! (P t).
Proof.
  intros T P; split.
  + intros w; simpl in *; apply w.
    intros t u; apply C_member.
  + intros w z t; apply W_member.
Defined.

Lemma Valid_markov_generalized : forall T P,
  (forall x, trivial_C (P x)) ->
  (forall x, trivial_W (P x)) ->
  Valid (markov_generalized T P).
Proof.
intros T P HC HW; split.
intros [w z]; apply rel_arr; simpl in *; intros Hr Hc.
let v := match goal with [ H : context [ w ?t ] |- _ ] => t end in
destruct (w v) as [t Ht].
let v := match goal with [ H : context [ w ?t ] |- _ ] => t end in
destruct (w v) as [u Hu].
simpl in *.
apply rel_not_not in Hr.
Qed.


  simpl in *.
  unfold valid, C, W; simpl; fold C; fold W.
  pose (u := fun (h : _ -> {x : t & W (p x)})  =>
    let y := projT1 (h (fun x (_ : W (p x)) => C_member (p x))) in
      existT (fun x : t => W (p x)) y (W_member (p y))).
  exists (u, fun _ x _ => C_member (p x)); simpl.
  intros [f g].
  simpl.
  set (v := projT1 (f (fun x _ => C_member (p x)))).
  set (w := projT2 (f (fun (x : t) (_ : W (p x)) => C_member (p x)))).
  rewrite (TC v (g v (W_member (p v)))).
  rewrite (TW v w).
  apply rel_not_not_stable.
Qed.

(** The usual Markov principle now follows easily. *)

Theorem markov (p : N -> bool) :
  valid (neg (all n : N, neg [p n]) ==> some n : N, [p n]).
Proof.
  intro p.
  apply markov_generalized with (t := N) (p := fun (n : N) => [p n]).
  intro; apply primitive_trivial_C.
  intro; apply primitive_trivial_W.
Qed.

(** ** The Independence of Premise *)

(** The usual IP relates propositional functions [p : s -> bool] and [q : t -> prp]:

   [((all x : s, p x) ==> some y : t, q y) ==> some y : t, (all x : s, p x) ==> q y]

   It is possible to generalize [p] to [p : s -> prp] with trival [W (p x)]. On the other
   hand, the type-dependencies force us to require that [C (q y)] be trivial. The proof
   below is unnecessarily complicated towards the end because I hit against a bug in
   [rewrite], see http://coq.inria.fr/bugs/show_bug.cgi?id=2061. *)

Theorem ip_generalized (s t : Inhabited) (p : s -> prp) (q : t -> prp) :
  (forall (x : s), trivial_W (p x)) ->
  (forall (y : t), trivial_C (q y)) ->
  valid (((all x : s, p x) ==> some y : t, q y) ==> some y : t, (all x : s, p x) ==> q y).
Proof.
  intros s t p q TW TC.
  unfold valid, C, W; simpl; fold C; fold W.
  pose (u := fun (x : s) => W_member (p x)).
  pose (v := fun (y : t) (w : W (q y)) => C_member (q y)).
  refine (existT _
          ((fun a => existT _ (projT1 (fst a u)) (fun _ => projT2 (fst a u),
                                                 (fun b => snd a (u, v)))),
           (fun _ => (u,v)))
          _).
  simpl.
  intros [[f g] h].
  simpl.
  set (y := projT1 (f u)).
  set (z := projT1 (g (u, v))).
  intros G.
  fold v.
  intro H.
  rewrite (TC y); simpl.
  rewrite (TC y (v y (projT2 (f u)))) in G; simpl in G.
  apply G.
  replace (u z) with (fst (h y (fun _ : forall x : s, W (p x) => projT2 (f u),
                                fun _ : (forall x : s, W (p x)) * C (q y) => g (u, v))) z).
  assumption.
  transitivity (member (inhabit (W_member (p z)))); apply (TW z).
Qed.

(** A special case of our IP occurs when [p] is a primitive propositional function. *)

Theorem ip (s t : Inhabited) (p : s -> bool) (q : t -> prp) :
  (forall (y : t), trivial_C (q y)) ->
  valid (((all x : s, [p x]) ==> some y : t, q y) ==> some y : t, (all x : s, [p x]) ==> q y).
Proof.
  intros s t p q TC.
  apply ip_generalized.
  intro; apply primitive_trivial_W.
  intro; apply TC.
Qed.

(** This concludes the verification of the Dialectica interpretation in Coq. There are at
   least three interesting directions to go:

   - Extract programs from the Dialectica interpretation. It looks like this could be done
     for extraction into Scheme. Extraction into Haskell and Ocaml seem more complicated
     because the [W] and [C] types are dependent and there seems no easy way of
     translating them into a simply-typed programming language. Presumably, concrete
     examples could be extracted with the help of "[Extraction Inline W C.]".

   - Explore other variants, such as the Diller-Nahm interpretation, or perhaps the
     interpretations a la Ulrich Kohlenbach and Paolo Oliva.

   - Explore the possibility of having a fully dependent Dialectica interpretation.
     Initial investigations by Thomas Streicher and myself indicate that it can be done.
     This would give us a way of constructing a two-level type system (with Prop separate
     from Set) that validates MP and IP. *)
