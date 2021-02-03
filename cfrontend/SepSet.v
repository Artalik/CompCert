From iris Require Export bi.bi proofmode.tactics proofmode.monpred.

From stdpp Require Export mapset gmap.

Definition pred_incl {A} (P Q : A -> Prop) := forall x, P x -> Q x.

Definition pred_impl {A} (P Q : A -> Prop) := fun x => P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).

Section hprop.

  (* Operators *)

  Context {X : Type}.
  Context {eqX : EqDecision X}.
  Context {countX : Countable X}.
  Definition hprop := gset X -> Prop.

  Definition hand (H1 H2 : hprop) : hprop :=
    fun h => H1 h /\ H2 h.

  Definition hor (H1 H2 : hprop) : hprop := fun h => H1 h \/ H2 h.

  Definition hempty : hprop := fun h => h = ∅.

  Definition hsingle l : hprop :=
    fun h =>  h = {[ l ]}.

  Definition set_ctx (ctx : gset X) : hprop := fun h => h = ctx.

  Definition hstar (H1 H2 : hprop) : hprop :=
    fun h => exists h1 h2, H1 h1 /\ H2 h2 /\ (h1 ## h2) /\ h = h1 ∪ h2.

  Definition hexists {A} (J : A -> hprop) : hprop := fun h => exists x, J x h.
  Definition hforall {A} (f : A -> hprop) : hprop := fun h => forall a, f a h.

  Definition hpure (P : Prop) : hprop := fun _ => P.

  Definition hpure_aff (P:Prop) : hprop := fun h => P /\ hempty h.

  Definition htop : hprop := fun h => True.

  Definition hwand (H1 H2 : hprop) : hprop :=
    hexists (fun (H:hprop) => (hstar H (hpure_aff ((hstar H H1) ==> H2)))).

  Definition qwand A (Q1 Q2:A->hprop) :=
    hforall (fun x => hwand (Q1 x) (Q2 x)).

  Lemma hempty_intro : hempty ∅.
  Proof using. reflexivity. Qed.

  Local Notation "'empty'" := (∅ : gset X).

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

  (* Lemma gset_disjoint_union_l_l : forall (h1 h2 h3 : gset X) , h1 ∪ h2 ## h3 -> h1 ## h3. *)
  (* Proof. *)
  (*   intros. apply disjoint_union_l in H as (P0&P1). assumption. *)
  (* Qed. *)

  (* Lemma heap_disjoint_union_l_r : forall (h1 h2 h3 :heap) , h1 ∪ h2 ##ₘ h3 -> h2 ##ₘ h3. *)
  (* Proof. *)
  (*   intros. apply map_disjoint_union_l in H as (P0&P1). assumption. *)
  (* Qed. *)

  (* Lemma heap_disjoint_union_r_r : forall (h1 h2 h3 :heap) , h1 ##ₘ h2 ∪ h3 -> h1 ##ₘ h3. *)
  (* Proof. *)
  (*   intros. apply map_disjoint_union_r in H as (P0&P1). assumption. *)
  (* Qed. *)

  (* Lemma heap_disjoint_union_r_l : forall (h1 h2 h3 :heap) , h1 ##ₘ h2 ∪ h3 -> h1 ##ₘ h2. *)
  (* Proof. *)
  (*   intros. apply map_disjoint_union_r in H as (P0&P1). assumption. *)
  (* Qed. *)

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

  Definition hpersistent (H:hprop) : hprop := fun h => H empty.

  Definition hlater (H : hprop) := H.

  Instance equiv_hprop : Equiv hprop.
  Proof.
    intros P0 P1. apply (forall h, P0 h <-> P1 h).
  Defined.

  Instance dist_hprop : Dist hprop.
  Proof.
    intros _ P0 P1. apply (forall h, P0 h <-> P1 h).
  Defined.

  Program Canonical Structure testofe := @Ofe hprop _ _ _.
  Next Obligation.
    split.
    - intros; split; intros; auto. apply (H 0).
    - intros; split; repeat intro; auto.
      + split; intro; apply H; auto.
      + split; intro.
        apply H0. apply H. auto.
        apply H. apply H0. auto.
    - intros. intro. apply H.
  Defined.

  Program Canonical Structure hpropI : bi :=
    Bi hprop _ _ pred_incl hempty hpure hand hor
       pred_impl (@hforall) (@hexists) hstar hwand hpersistent hlater _ _ _ _.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intros H h P. assumption.
    - rewrite /Transitive. intros. intros h P. eauto.
    - repeat intro. apply H. auto.
    - repeat intro. apply H. auto.
    - destruct H; intro; apply H; auto.
    - destruct H; intro; apply H0; auto.
    - intro; apply H; auto.
    - intro. apply H; auto.
    - destruct H1. apply H. auto.
    - apply H0. destruct H1. auto.
    - apply H. destruct H1. auto.
    - apply H0. destruct H1. auto.
    - intro. destruct H1. left. apply H. auto. right. apply H0. auto.
    - intro. destruct H1. left. apply H. auto. right. apply H0. auto.
    - repeat intro. apply H0. apply H1. apply H. auto.
    - repeat intro. apply H0. apply H1. apply H. auto.
    - repeat intro. apply H. apply H0.
    - repeat intro. apply H. apply H0.
    - repeat intro. edestruct H0. exists x0. apply H. apply H1.
    - repeat intro. edestruct H0. exists x0. apply H. apply H1.
    - intros. inversion_star h P. exists h0, h1. repeat split; auto. apply H; auto. apply H0; auto.
    - intros. inversion_star h P. exists h0, h1. repeat split; auto. apply H; auto. apply H0; auto.
    - rewrite /hwand. repeat intro. destruct H1. inversion_star h P.
      exists x1, h0, h1. destruct P1. repeat split; auto. repeat intro. inversion_star h P.
      apply H0. apply H2. exists h2, h3. repeat split; auto. apply H. auto.
    - rewrite /hwand. repeat intro. destruct H1. inversion_star h P.
      exists x1, h0, h1. destruct P1. repeat split; auto. repeat intro. inversion_star h P.
      apply H0. apply H2. exists h2, h3. repeat split; auto. apply H. auto.
    - intro. apply H. apply H0.
    - intro. apply H. apply H0.
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
    - intros x W A. exists empty; exists W. repeat split; auto.
      apply disjoint_empty_l. rewrite union_empty_l_L. auto.
    - intros P h Q. inversion_star H H. inversion H3. subst.
      rewrite union_empty_l_L. apply H4.
    - intros P Q h R. inversion_star H H. exists H2; exists H0. repeat split; auto. subst.
      apply union_comm_L.
    - intros P Q R h P0. inversion_star h P. clear P0. inversion_star h P. clear P2.
      exists h2. exists (h3 ∪ h1). repeat split; auto. exists h3, h1. repeat split; auto.
      subst. eapply disjoint_union_l; eauto. eapply disjoint_union_r. subst.
      split; auto. eapply disjoint_union_l. rewrite union_comm. eauto.
      subst. rewrite union_assoc_L. auto.
    - intros P Q R P0 h P1. exists P. exists h; exists empty. repeat split; auto.
      apply disjoint_empty_r. rewrite union_empty_r_L. auto.
    - intros P Q R W h P0. inversion_star h P. apply W in P2. destruct P2. inversion_star h H.
      inversion H2. apply H4. exists h2; exists h1. repeat split; auto; subst.
      + apply disjoint_union_l in P4. apply P4.
      + inversion H5. subst. rewrite union_empty_r_L. auto.
    - rewrite /hpersistent. intros P Q H h P0. apply H. apply P0.
    - rewrite /hpersistent. rewrite /hforall. intros A B C D E. apply D.
    - rewrite /hpersistent. intros P Q h P0. inversion_star h P. apply P2.
    - intros P Q x W. destruct W. exists empty; exists x. repeat split; auto.
      apply disjoint_empty_l. rewrite union_empty_l_L. auto.
  Qed.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intro. apply H. auto.
    - intro. apply H. auto.
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

  Definition ctx (h : gset X) : monPred biInd hpropI := MonPred (fun _ => set_ctx h) _.

  Ltac inv H := inversion H; clear H; subst.

  Local Open Scope bi_scope.

  Local Notation "'&&' l" :=
    (ctx l) (at level 20) : bi_scope.

  Local Notation "'&' l" :=
    (single l) (at level 20) : bi_scope.

  Lemma singleton_neq : forall l l', ⊢ & l -∗ & l' -∗ ⌜l ≠ l'⌝.
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red. intros. destruct i. destruct a. clear H0.
    inv H. exists emp, empty, empty. repeat split; auto.
    intros h H j C. clear C. clear j. inversion_star h P. clear H. inv P0. clear P2.
    red in P1. rewrite union_empty_l_L. exists (set_ctx h1), h1, empty.
    repeat split; eauto. subst. intros h H eq. inversion_star h P. clear H.
    red in P1. red in P0. subst. erewrite disjoint_singleton_l in P2. apply P2.
    apply lookup_singleton. apply disjoint_empty_r. rewrite union_empty_r_L. auto.
    apply disjoint_empty_r. rewrite union_empty_r_L. auto.
  Qed.

  Lemma emp_trivial : ⊢ (emp : monPred biInd hpropI). simpl. auto. Qed.

  Global Instance affine_heap_empty : Affine (ctx ∅).
  Proof.
    split. intro. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Lemma init_heap : ⊢ ctx ∅.
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
    - MonPred.unseal. reflexivity.
    - repeat red. repeat split; auto.
    - inversion_star h P. inversion P1. apply H1. exists empty; exists h.
      inversion H2; subst. rewrite union_empty_r_L in P; subst.
      repeat split; auto. apply disjoint_empty_l. rewrite union_empty_l_L. auto.
  Qed.

  Lemma completeness (Φ : iProp) h : Φ () h -> (⊢&& h -∗ Φ).
  Proof.
    MonPred.unseal. split. MonPred.unseal. simpl. repeat red. intros. exists emp. exists x; exists empty.
    repeat split; auto.
    intros h0 P0. inversion_star h P. simpl in *. rewrite <- P2 in *. inversion P1.
    subst. rewrite union_empty_l_L. rewrite <- P2. destruct a. apply H.
    apply disjoint_empty_r. rewrite union_empty_r_L. auto.
  Qed.

  Lemma equivalence (Φ : iProp) h : Φ () h <-> (⊢&& h -∗ Φ).
  Proof.
    split.
    apply completeness.
    apply soundness.
  Qed.

  Lemma heap_ctx_split (h h' : gset X) : h ## h' -> (⊢&& (h \u h') -∗ && h ∗ && h').
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red.
    intros. exists hempty. inversion H0; subst.
    exists empty; exists empty. repeat split; auto.
    + repeat intro. inversion_star h P. inversion P1. subst.
      exists h; exists h'. repeat split; auto. inversion P0; subst.
      rewrite union_empty_l_L. reflexivity.
    + apply disjoint_empty_l.
    + rewrite union_empty_l_L. reflexivity.
  Qed.

  Lemma heap_ctx_split_sing (h : gset X) l : h ## ({[ l ]}) ->
                                             (⊢&& ({[ l ]} \u h) -∗ && h ∗ & l).
  Proof.
    iIntros (?) "HA". iApply heap_ctx_split; auto. rewrite union_comm_L. auto.
  Qed.

End hprop.

Notation "'empty'" := (∅ : gset).

Notation "'\[]'" := (hempty) (at level 0).

Notation "\[ P ]" := (hpure P) (at level 0, P at level 99, format "\[ P ]").

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

Notation "\Top" := htop.


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
  (ctx h) (at level 20).
