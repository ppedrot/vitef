Require Import dialectica.

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
