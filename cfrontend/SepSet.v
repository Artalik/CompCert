Require Import FunctionalExtensionality.

From iris Require Export bi.bi proofmode.tactics proofmode.monpred.

From stdpp Require Export gmap.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.
Definition pred_incl {A} (P Q : A -> Prop) := forall x, P x -> Q x.

Definition pred_impl {A} (P Q : A -> Prop) := fun x => P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).

Section hprop.
  (* Operators *)
(* =hprop= *)
Context {X : Type}.
Context {eqX : EqDecision X}.
Context {count_X : Countable X}.
Definition heap : Type := gmap X unit.
(* =end= *)

  Definition hprop := heap -> Prop.

  Definition hand (H1 H2 : hprop) : hprop :=
    fun h => H1 h /\ H2 h.

  Definition hor (H1 H2 : hprop) : hprop := fun h => H1 h \/ H2 h.

  Definition hempty : hprop := fun h => h = ∅.

(* =hsingle= *)
Definition hsingle l : hprop :=
  fun h =>  h = {[l := tt]}.
(* =end= *)

  Definition hheap_ctx (ctx : heap) : hprop := fun h => h = ctx.
Notation "n '##' m" := (n ##ₘ m).
(* =hstar= *)
Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1 /\ H2 h2 /\ (h1 ## h2) /\ h = h1 ∪ h2.
(* =end= *)
(* =hquantifier= *)
Definition hexists {A} (J : A -> hprop) : hprop := fun h => exists x, J x h.
Definition hforall {A} (f : A -> hprop) : hprop := fun h => forall a, f a h.
(* =end= *)

(* =hpure= *)
Definition hpure (P : Prop) : hprop := fun _ => P.
(* =end= *)

  Definition hpure_aff (P:Prop) : hprop := fun h => P /\ hempty h.

  Definition htop : hprop := fun h => True.

  Definition hwand (H1 H2 : hprop) : hprop :=
    hexists (fun (H:hprop) => (hstar H (hpure_aff ((hstar H H1) ==> H2)))).

  Definition qwand A (Q1 Q2:A->hprop) :=
    hforall (fun x => hwand (Q1 x) (Q2 x)).

  Lemma hempty_intro : hempty ∅.
  Proof using. reflexivity. Qed.

  Local Notation "'heap_empty'" := (∅ : heap).

  Local Notation "h1 \u h2" := (h1 ∪ h2) (at level 37, right associativity).

  Local Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
                                         (at level 39, x1 name, H at level 50).
  Local Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                            (at level 39, x1 name, x2 name, H at level 50).
  Local Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                               (at level 39, x1 name, x2 name, x3 name, H at level 50).


  Local Notation "'\[]'" := (hempty)
                              (at level 0).

  Local Notation "\[ P ]" := (hpure P)
                               (at level 0, P at level 99, format "\[ P ]").

  Local Notation "H1 '\*' H2" := (hstar H1 H2)
                                   (at level 41, right associativity).

  Local Notation "\Top" := htop.

  (* Properties on heap *)
  Instance heap_union_empty_l : LeftId (=@{heap}) ∅ (∪) := _.
  Instance heap_union_empty_r : RightId (=@{heap}) ∅ (∪) := _.
  Instance heap_union_assoc : base.Assoc (=@{heap}) (∪).
  Proof.
    intros m1 m2 m3. unfold base.union, map_union, union_with, map_union_with.
    apply (merge_assoc _). intros i.
    unfold heap in m1. unfold heap in m2. unfold heap in m3.
      by destruct (m1 !! i), (m2 !! i), (m3 !! i).
  Qed.

  Definition heap_union_comm (h1 h2 : heap) := map_union_comm h1 h2.

  Lemma heap_disjoint_union_l_l : forall (h1 h2 h3 :heap) , h1 ∪ h2 ##ₘ h3 -> h1 ##ₘ h3.
  Proof.
    intros. apply map_disjoint_union_l in H as (P0&P1). assumption.
  Qed.

  Lemma heap_disjoint_union_l_r : forall (h1 h2 h3 :heap) , h1 ∪ h2 ##ₘ h3 -> h2 ##ₘ h3.
  Proof.
    intros. apply map_disjoint_union_l in H as (P0&P1). assumption.
  Qed.

  Lemma heap_disjoint_union_r_r : forall (h1 h2 h3 :heap) , h1 ##ₘ h2 ∪ h3 -> h1 ##ₘ h3.
  Proof.
    intros. apply map_disjoint_union_r in H as (P0&P1). assumption.
  Qed.

  Lemma heap_disjoint_union_r_l : forall (h1 h2 h3 :heap) , h1 ##ₘ h2 ∪ h3 -> h1 ##ₘ h2.
  Proof.
    intros. apply map_disjoint_union_r in H as (P0&P1). assumption.
  Qed.

  Declare Scope heap_scope.

  Hint Resolve heap_union_empty_l heap_union_empty_r hempty_intro map_disjoint_empty_l map_disjoint_empty_r heap_union_assoc heap_disjoint_union_r_l heap_disjoint_union_l_l heap_disjoint_union_r_r heap_disjoint_union_l_r : heap_scope.

  Ltac inversion_star h P :=
    match goal with
    | H : (_ \* _) _ |- _ =>
      let W := fresh h in
      let w := fresh P in
      inversion H as (W&w);
      let W := fresh h in
      destruct w as (W&w);
      do 3 (let w0 := fresh P in
            destruct w as (w0&w))
    end.
  Ltac extens := apply functional_extensionality; intro; apply prop_extensionality.

  Section Properties.

    Lemma hstar_comm : forall H1 H2,
      H1 \* H2 = H2 \* H1.
    Proof using.
      intros H1 H2. extens.
      split; intro P; inversion_star h P; exists h0; exists h; repeat split; auto;
        rewrite heap_union_comm; auto.
    Qed.

    Lemma hstar_assoc : forall H1 H2 H3,
        (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
    Proof using.
      intros H1 H2 H3. extens. split.
      { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
        exists h1; exists (h2 ∪ h3). repeat split; auto.
        { exists h2; exists h3; eauto with heap_scope. }
        { apply map_disjoint_union_l in D as (P0&P1).
          apply map_disjoint_union_r. split; auto. }
        { by rewrite heap_union_assoc. }}
      { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
        exists (h1 ∪ h2); exists h3. repeat split; auto.
        { exists h1; exists h2; eauto with heap_scope. }
        { rewrite map_disjoint_union_l. split; auto.
          apply map_disjoint_union_r in D as (P0&P1).
          assumption. }
          by rewrite <- heap_union_assoc. }
    Qed.

  End Properties.

  Definition hpersistent (H:hprop) : hprop := fun h => H heap_empty.

  Definition hlater (H : hprop) := H.

  Set Warnings "-redundant-canonical-projection -convert_concl_no_check".
  Canonical Structure hpropO := leibnizO hprop.

  Program Canonical Structure hpropI : bi :=
    Bi hprop _ _ pred_incl hempty hpure hand hor
       pred_impl (@hforall) (@hexists) hstar hwand hpersistent hlater _ _ _ _.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intros H h P. assumption.
    - rewrite /Transitive. intros. intros h P. eauto.
    - rewrite leibniz_equiv_iff. intros (P0&P1). extens. split; intro; auto.
    - intros n P0 P1 Z. rewrite /hpure. repeat red. extens. auto.
    - intros n P0 P1 Z. rewrite /hforall. repeat red. intros. extens.
      split; intros; repeat red in H; apply functional_extensionality in H; subst; auto.
    - intros n P0 P1 Z. rewrite /hexists. repeat red. intros. extens.
      split; intro; repeat red in H; apply functional_extensionality in H; subst; auto.
    - rewrite /hpure. intros φ P imp h P0. apply imp; auto.
    - rewrite /hand. intros P Q h (P0&P1). apply P0.
    - rewrite /hand. intros P Q h (P0&P1). apply P1.
    - rewrite /hor. intros P Q h P0. auto.
    - rewrite /hor. intros P Q h P0. auto.
    - rewrite /hor. intros P Q h P0 P1 h0 P2. destruct P2; auto.
    - intros P Q R P0 h P2 P3. apply P0. split; auto.
    - intros P Q R P0 h P2. destruct P2. apply P0 in H. apply H in H0. auto.
    - intros x W a H h P h0. apply H. apply P.
    - intros h Q a H H0. apply H0.
    - intros x W H P Q. exists H. apply Q.
    - intros x W Q P h P0. destruct P0. eapply P. apply H.
    - intros P P' Q Q' A B C D. inversion_star h P. exists h; exists h0. repeat split; auto.
    - intros x W A. exists heap_empty; exists W. repeat split; auto with heap_scope.
      apply map_disjoint_empty_l.
    - intros P h Q. inversion_star H H. inversion H3. subst.
      rewrite heap_union_empty_l. apply H4.
    - intros P Q h R. inversion_star H H. exists H2; exists H0. repeat split; auto. subst.
      apply heap_union_comm. apply H5.
    - intros P Q R h P0. rewrite <- hstar_assoc. apply P0.
    - intros P Q R P0 h P1. exists P. exists h; exists heap_empty. repeat split; auto with heap_scope.
      apply map_disjoint_empty_r.
    - intros P Q R W h P0. inversion_star h P. apply W in P2. destruct P2. inversion_star h H.
      inversion H2. apply H4. exists h2; exists h1. repeat split; auto; subst.
      + apply heap_disjoint_union_l_l in P4. apply P4.
      + inversion H5. subst. rewrite heap_union_empty_r. reflexivity.
    - rewrite /hpersistent. intros P Q H h P0. apply H. apply P0.
    - rewrite /hpersistent. rewrite /hforall. intros A B C D E. apply D.
    - rewrite /hpersistent. intros P Q h P0. inversion_star h P. apply P2.
    - intros P Q x W. destruct W. exists heap_empty; exists x. repeat split; auto with heap_scope.
      apply map_disjoint_empty_l.
  Qed.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intros A Φ h a. rewrite /hlater. unfold hforall in *. unfold hlater in a. apply a.
    - intros A Φ h a. rewrite /hor. unfold hlater in *. destruct a. right. exists x. apply H.
    - intros Hp h P. unfold hlater in *. right. intro. apply P.
  Qed.

  Instance inhabited_unit : Inhabited unit.
  Proof.
    split. apply ().
  Qed.

  Instance PreOrder_unit : PreOrder (fun (t1 t2 : unit) => t1 = t2).
  Proof.
    split; repeat red; intros; trivial. destruct x,y,z. reflexivity.
  Qed.

  Program Canonical Structure biInd := BiIndex unit inhabited_unit _ PreOrder_unit.

  Definition single (l : X) : @monPred biInd hpropI := MonPred (fun _ => hsingle l) _.

  Definition heap_ctx (h : heap) : monPred biInd hpropI := MonPred (fun _ => hheap_ctx h) _.

  Ltac inv H := inversion H; clear H; subst.

  Local Open Scope bi_scope.

  Local Notation "'&&' l" :=
    (heap_ctx l) (at level 20) : bi_scope.

  Local Notation "'&' l" :=
    (single l) (at level 20) : bi_scope.

(* =neq= *)
Lemma singleton_neq : forall l l', ⊢ & l -∗ & l' -∗ ⌜l ≠ l'⌝.
(* =end= *)
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red. intros. destruct i. destruct a. clear H0.
    inv H. exists emp, heap_empty, heap_empty. repeat split; auto with heap_scope.
    intros h H j C. clear C. clear j. inversion_star h P. clear H. inv P0. clear P2.
    red in P1. rewrite heap_union_empty_l. exists (hheap_ctx h1), h1, heap_empty.
    repeat split; eauto with heap_scope. subst. intros h H eq. inversion_star h P. clear H.
    red in P1. red in P0. subst. erewrite map_disjoint_spec in P2.
    edestruct P2; eapply lookup_singleton_Some; eauto.
    apply map_disjoint_empty_r.
  Qed.

  Lemma emp_trivial : ⊢ (emp : monPred biInd hpropI). simpl. auto. Qed.

  Global Instance affine_heap_empty : Affine (heap_ctx ∅).
  Proof.
    split. intro. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Lemma init_heap : ⊢ heap_ctx ∅.
  Proof.
    split. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Lemma instance_heap : forall (P : monPred biInd hpropI) (Q : Prop), (forall tmps, P () tmps -> Q) -> (P ⊢ ⌜Q⌝).
  Proof.
    MonPred.unseal. intros. split. repeat red. intros.
    eapply H. destruct i. eapply H0.
  Qed.

  Lemma soundness_pure h (Φ : Prop) : (&& h ⊢ (⌜ Φ ⌝) : monPred biInd hpropI) -> Φ.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (e := H () h). eapply e. reflexivity.
  Qed.

  Definition iProp := monPred biInd hpropI.

  Lemma soundness (Φ : iProp) h : (⊢&& h -∗ Φ) -> Φ () h.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (e := H () ∅).
    simpl in *. edestruct e.
    - rewrite monPred_at_emp. split; auto; apply hempty_intro.
    - repeat red. repeat split; auto.
    - inversion_star h P.
      inversion P1.
      apply H1.
      exists heap_empty; exists h.
      inversion H2; subst. rewrite heap_union_empty_r in P; subst.
      repeat split; auto. apply map_disjoint_empty_l. rewrite heap_union_empty_l. auto.
  Qed.

  Lemma completeness (Φ : iProp) h : Φ () h -> (⊢&& h -∗ Φ).
  Proof.
    MonPred.unseal. split. MonPred.unseal. simpl. repeat red. intros. exists emp. exists x; exists heap_empty.
    repeat split; auto with heap_scope.
    intros h0 P0. inversion_star h P. simpl in *. rewrite <- P2 in *. inversion P1.
    subst. rewrite heap_union_empty_l. rewrite <- P2. destruct a. apply H.
    apply map_disjoint_empty_r.
  Qed.

(* =equivalence= *)
Lemma equivalence (Φ : iProp) h : Φ () h <-> (⊢&& h -∗ Φ).
(* =end *)
  Proof.
    split.
    apply completeness.
    apply soundness.
  Qed.

  Lemma heap_ctx_split (h h' : heap) : h ##ₘ h' -> (⊢&& (h \u h') -∗ && h ∗ && h').
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red.
    intros. exists hempty. inversion H0; subst.
    exists heap_empty; exists heap_empty. repeat split; auto.
    + repeat intro. inversion_star h P. inversion P1. subst.
      exists h; exists h'. repeat split; auto. inversion P0; subst.
      rewrite heap_union_empty_l. reflexivity.
    + rewrite heap_union_empty_l. reflexivity.
  Qed.

  Lemma heap_ctx_split_sing (h : heap) l : h ##ₘ ({[l := tt]}) ->
                                             (⊢&& (<[l := tt]>h) -∗ && h ∗ & l).
  Proof.
    iIntros (?) "HA". rewrite insert_union_singleton_r; auto. iApply heap_ctx_split; auto.
    rewrite <- map_disjoint_singleton_r. eauto.
  Qed.

End hprop.

Notation "'heap_empty'" := (∅ : heap).

Notation "'\[]'" := (hempty) (at level 0).

(* =hpure_notation= *)
Notation "\[ P ]" := (hpure P) (at level 0, P at level 99, format "\[ P ]").
(* =end= *)

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

Notation "\Top" := htop.


Declare Scope heap_scope.

Global Hint Resolve heap_union_empty_l heap_union_empty_r hempty_intro map_disjoint_empty_l map_disjoint_empty_r heap_union_assoc heap_disjoint_union_r_l heap_disjoint_union_l_l heap_disjoint_union_r_r heap_disjoint_union_l_r : heap_scope.

Ltac inversion_star h P :=
  match goal with
  | H : (_ \* _) _ |- _ =>
    let W := fresh h in
    let w := fresh P in
    inversion H as (W&w);
    let W := fresh h in
    destruct w as (W&w);
    do 3 (let w0 := fresh P in
          destruct w as (w0&w))
  end.

Open Scope bi_scope.

Notation "'&' l" :=
  (single l) (at level 20).

Notation "'&&' h" :=
  (heap_ctx h) (at level 20).
