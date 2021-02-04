Require Import List Lia.
Require Import tree.
Require Import freefresh.
Require Import fresh.

Section WP.
Variable X: Type.
Implicit Type m: FreeFresh X.

(* =wp= *)
Fixpoint wp (m: FreeFresh X)(Q: X -> nat -> Prop): nat -> Prop :=
  match m with
  | ret v => fun n => Q v n
  | gensymOp _ k => fun n => wp (k n) Q (1+n)
  end.
(* =end= *)

End WP.

Arguments wp [_] m Q.

Section Soundness.
Variable X: Type.
Implicit Type m: FreeFresh X.
Implicit Type Q: X -> nat -> Prop.
Implicit Type n: nat.
Implicit Type v: X.

(* =soundness= *)
Lemma adequacy: forall m Q n n' v,
    wp m Q n -> eval m n = (v, n') -> Q v n'.
(* =end= *)
Proof.
  induction m; intros.
  - inversion H0; subst. apply H.
  - simpl in *. destruct u. eapply H; eauto.
Qed.

End Soundness.

Axiom right_unit    : forall {X} (a : FreeFresh X), do v <- a; ret! v = a.
Axiom left_unit     : forall {X Y} (a : X) (f : X -> FreeFresh Y), do v <- ret! a; f v = f a.
Axiom associativity : forall {A B C} (m : FreeFresh A) (f : A -> FreeFresh B) (g : B -> FreeFresh C),
       do v' <- (do v <- m; f v); g v' =
       do v <- m; do v' <- f v; g v'.

Lemma wp_bind : forall {X Y} Q (f : FreeFresh X) (g : X -> FreeFresh Y) n,
    wp f (fun x => wp (g x) Q) n -> wp (do v <- f; g v) Q n.
Proof.
  induction f; intros.
  - rewrite left_unit. apply H.
  - simpl in *. destruct u. apply H. exact H0.
Qed.

Lemma wp_consequence : forall {X} (P Q : X -> nat -> Prop) (f : FreeFresh X) n,
    wp f P n ->
    (forall x n, P x n -> Q x n) ->
    wp f Q n.
Proof.
  induction f; simpl; intros.
  - apply (H0 x n H).
  - destruct u. apply (H _ _ H0 H1).
Qed.

Lemma wp_ret : forall {X} (P : X -> nat -> Prop) (v : X) n,
    P v n -> wp (ret! v) P n.
Proof.
  intros. exact H.
Qed.

Lemma wp_gensym : forall n,
    wp (gensym tt) (fun v n' => v = n /\ n' = 1+n) n.
Proof.
  intros. simpl. split; reflexivity.
Qed.


(* =triple= *)
Notation "{{ P }} m {{ Q }}" := (forall n, P n -> wp m Q n)
(* =end= *)
    (at level 20, format "'[hv' {{  P  }}  '/  ' m '/'  {{ Q  }} ']'").

Section Rules.
Variables X Y: Type.
Implicit Type m: FreeFresh X.
Implicit Type f: X -> FreeFresh Y.
Implicit Type P : nat -> Prop.
Implicit Type Q: X -> nat -> Prop.
Implicit Type R: Y -> nat -> Prop.
Implicit Type x: X.

(* =rule_value= *)
Lemma rule_value: forall Q v,

    (*-----------------------*)
    {{ Q v }} ret! v {{ Q }}.
(* =end= *)
Proof. auto. Qed.

(* =rule_composition= *)
Lemma rule_composition: forall m f P Q R,

    {{ P }} m {{ Q }} ->
    (forall v, {{ Q v }} f v  {{ R }}) ->
    (*-------------------------------*)
    {{ P }} do x <- m; f x {{ R }}.
(* =end= *)
Proof.
  induction m; simpl; intros.
  - eapply H0; eapply H; auto.
  - eapply H; eauto.
Qed.

(* =rule_fresh= *)
Lemma rule_gensym: forall k,

    (*-------------------------------------------------------*)
    {{ fun n => n = k }} gensym tt {{fun v n' => v = k /\ n' = 1+k}}.
(* =end= *)
Proof.
  intros. simpl. repeat split; auto.
Qed.

(* =rule_consequence= *)
Lemma rule_consequence P P' Q Q'  m:

    {{ P' }} m {{ Q' }} ->
    (forall n, P n -> P' n) ->
    (forall x n, Q' x n -> Q x n) ->
    (*-----------------------*)
    {{ P }} m {{ Q }}.
(* =end= *)
Proof.
  revert P P' Q Q'.
  induction m; simpl; intros.
  - apply (H1 _ _ (H _ (H0 _ H2))).
  - destruct u.
    eapply (H _ (fun k => k = S n) (fun k => P (k-1) /\ k = 1+n) _ Q').
    + intros n0 [P0 P1]. subst. eapply H0. apply H1. apply H3.
    + intros. subst. split; auto. simpl.  assert (n - 0 = n) by lia. rewrite H4. apply H3.
    + apply H2.
    + reflexivity.
Qed.

End Rules.

Fixpoint flatten {X} (t : Tree X) : list X :=
  match t with
  | Leaf e => e :: nil
  | Node l r => flatten l ++ flatten r
  end.

Lemma NoDupTree : forall n t n', flatten t = seq n n' -> NoDup (flatten t).
Proof.
  intros n t n' P1. rewrite P1. apply seq_NoDup.
Qed.

Section Label_Spec.

Variable X: Type.
Implicit Type t: Tree X.

Fixpoint size {X} (t : Tree X) : nat :=
  match t with
  | Leaf _ => 1
  | Node l r => (size l) + size r
  end.

Lemma label_spec_aux: forall t k,
    {{ fun n => n = k }}
      label t
      {{ fun ft n' => k + size ft = n' /\ flatten ft = seq k (size ft) }}.
Proof.
  induction t.
  - intros. simpl. subst. split. lia. auto.
  - intros. simpl label. apply wp_bind.
    eapply wp_consequence. eapply IHt1. eauto. intro.
    intros. apply wp_bind. simpl in *. destruct H0.
    eapply wp_consequence. eapply IHt2. eauto. intros.
    simpl in *. destruct H2. split. lia.
    rewrite H1. rewrite H3. rewrite <- H0. rewrite <- seq_app. auto.
Qed.

Lemma size_positive : forall X (t : Tree X), 0 < size t.
Proof.
  induction t; simpl; lia.
Qed.

Definition interval a b := seq a (1 + b - a).


(* =label_spec= *)
Lemma label_spec: forall t k,
    {{ fun n => n = k }}
      label t
    {{ fun ft n' => k < n' /\ flatten ft = interval k (n'-1) }}.
(* =end= *)
Proof.
  intros t k. eapply rule_consequence.
  - eapply label_spec_aux.
  - simpl. eauto.
  - simpl. intros. pose (size_positive nat x). destruct H. split. rewrite <- H.
    pose (size_positive nat x). lia.
    unfold interval. rewrite <- H.
    assert (1 + (k + size x - 1) - k = size x) by lia.
    rewrite H1. auto.
Qed.

End Label_Spec.
