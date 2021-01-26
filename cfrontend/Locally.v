Require Import MoSel.
Import weakestpre_gensym.
Export Maps.PTree.

Notation "a ! b" := (get b a) (at level 1).

Definition hlocally {A} (le : t A) (f : t A -> iProp) : hprop :=
  fun h => forall le', (forall id, In id h -> le ! id = le' ! id) -> f le' () h.

Definition locally {A} (le : t A) (f : t A -> iProp) : iProp := MonPred (fun _ => hlocally le f) _.


(** Useful invariance properties. *)
Ltac inv H := inversion H; clear H; subst.

Ltac unfold_locally :=
unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
    destruct i; inv H; repeat red; intros a b; destruct a; clear b; exists emp, nil, nil;
      repeat split; auto; [intros h H0; inversion_star h H; clear H0; inversion H1; subst; simpl in *
                          | intros x y P0 P1; inversion P0].

Lemma locally_base {A} : forall (le : t A), ⊢ locally le (fun le' => emp).
Proof.
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H.
  intros. inv H. reflexivity.
Qed.

Lemma locally_elim {A} : forall P (le : t A), ⊢ locally le (fun le' => P le') -∗ P le.
Proof.
  unfold_locally.
  eapply prop_eq; eauto. apply list_eq_comm. auto.
Qed.

Lemma locally_consequence {A} : forall (P Q : t A -> iProp) (le : t A),
    ⊢locally le (λ le', P le') -∗ (∀ le, P le -∗ Q le) -∗ locally le (λ le', Q le').
Proof.
  unfold_locally. clear H3. intros j P0. destruct j. clear P0.
  repeat red. exists (hheap_ctx h), h, nil. repeat split; auto.
  red. intros. inversion_star h P. clear H0. red in P1. subst.
  edestruct P2. reflexivity. inversion_star h P.
  clear H0. destruct P6. inv H4. clear P7. rewrite app_nil_r in P4.
  apply H0. exists h3, h0. repeat split; auto. eapply prop_eq; eauto. apply list_eq_comm. eauto.
  eapply prop_eq. apply list_eq_comm. eauto. eapply H2. intros. erewrite <- H3; auto.
  apply P0. apply in_or_app. left. apply P1. apply H; auto.
  eapply list_eq_disjoint. apply list_eq_comm. eauto. apply list_disjoint_comm. auto.
  intros. apply P0 in H4. apply in_app_or in H4. destruct H4; apply in_or_app.
  right; auto. left; auto. apply P4; auto. intros. apply P0. apply in_app_or in H4.
  destruct H4; apply in_or_app; auto. right. apply P4; auto.
  intros x y P0 P1. inversion P1.
  all : rewrite <- app_nil_end; auto.
Qed.

Lemma locally_consequence_2 {A} : forall P Q (le : t A),
    ⊢ (∀ le, P le -∗ Q le) -∗ locally le (λ le', P le') -∗ locally le (λ le', Q le').
Proof.
  iIntros "* HA HB". iApply (locally_consequence with "HB HA"); eauto.
Qed.

Lemma locally_sep {A} : forall P R (le : t A),
    ⊢locally le (fun le' => P le') -∗ locally le (fun le' => R le') -∗
            locally le (fun le' => P le' ∗ R le').
Proof.
  unfold_locally. intros j P0. destruct j. clear P0 H3 H1.
  exists (hheap_ctx h), h, nil. repeat split; auto.
  repeat red. intros. inversion_star h P. clear H0. red in P1. subst.
  exists h1, h2. repeat split; auto. apply H2.
  intros. eapply H1. apply P0. apply in_or_app. left. apply P1. apply H; auto.
  apply P2. intros. apply H1. apply P0. apply in_or_app. right. auto.
  eapply list_eq_disjoint; eauto. apply list_eq_comm. intro. split; intro.
  apply H. apply P1; auto. apply P1. apply H; auto.
  intros. apply P0 in H0. apply in_app_or in H0. destruct H0; apply in_or_app.
  left. apply H; auto. apply P1; auto. right; auto.
  intros. apply P0. apply in_app_or in H0. destruct H0; apply in_or_app.
  left. apply P1. apply H; auto. right; auto.
  intros x y P0 P1. inversion P1.
  all : rewrite <- app_nil_end; auto.
Qed.

Lemma locally_and {A} : forall P R (le : t A),
    ⊢locally le (fun le' => P le') ∧ locally le (fun le' => R le') -∗
            locally le (fun le' => P le' ∧ R le').
Proof.
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
  destruct i; inversion H as (H0); clear H; subst. intros j H; destruct j; clear H.
  exists emp, nil, nil; repeat split; auto.
  3 : intros x y P0 P1; inversion P0.
  1-2 :inversion_star h P; clear H;
    destruct P2; inv P1; clear P3; simpl in *; apply list_eq_comm in P0; eapply prop_eq; eauto.
  apply H. intros. apply H0. apply P0. auto.
  apply H1. intros. apply H0. apply P0. auto.
Qed.

Lemma locally_simpl {A} : forall P (le : t A), ⊢(∀ le', P le') -∗ locally le (fun le' => P le').
Proof.
  iIntros "* HA". iApply locally_consequence. iApply locally_base. iIntros "* _". iApply "HA".
Qed.

Lemma locally_indep {A} : forall (P : iProp) (le : t A), ⊢P -∗ locally le (fun _ => P).
Proof.
  iIntros. iApply locally_simpl. auto.
Qed.


Lemma locally_indep_frame {A} : forall P R (Q : iProp) (le : t A),
    ⊢locally le (fun le' => P le' -∗ R le') -∗ locally le (fun le' => P le' ∗ Q -∗ R le' ∗ Q).
Proof.
  iIntros "* HA". iApply locally_consequence_2; eauto.
  iIntros "* HA [HB $]". iApply ("HA" with "HB").
Qed.

Lemma locally_modout {A} : forall P (le : t A),
    ⊢<absorb> (locally le (fun le' => P le')) -∗ locally le (fun le' => <absorb> P le').
Proof.
  unfold_locally. clear H3. red in H2. inversion_star h P. clear H2.
  exists h0, h2. repeat split; auto. apply P2. intros. eapply H0. apply H. apply P0.
  apply in_or_app. right; auto.
  intros. apply H in H2. apply P0 in H2. auto.
  intros. apply H. apply P0. auto.
Qed.

Lemma locally_idempotence {A} : forall P (le : t A),
    ⊢locally le (fun le' => P le') -∗ locally le (fun le' => locally le' (fun le'' => P le'')).
Proof.
  unfold_locally. intros. eapply prop_eq. apply list_eq_comm. eauto. apply H2.
  intros. apply H in H5. pose H5. apply H0 in i. apply H4 in H5.
  etransitivity; eauto.
Qed.

Lemma locally_sep_indep_r {A} : forall P Q (le : t A),
    ⊢locally le (fun le' => P le') ∗ Q -∗ locally le (fun le' => P le' ∗ Q).
Proof.
  iIntros "* [HA HB]". iApply (locally_sep with "HA"). iApply locally_indep. iFrame.
Qed.

Lemma locally_sep_indep_l {A} : forall P Q (le : t A),
    ⊢locally le (fun le' => P le') ∗ Q -∗ locally le (fun le' => Q ∗ P le').
Proof.
  iIntros "* [HA HB]". iApply (locally_sep with "[HB] HA"). iApply locally_indep. iFrame.
Qed.

Lemma locally_forall {A B} : forall P (le : t A),
    ⊢(∀ l, locally le (fun le' => P l le')) -∗ locally le (fun le' => ∀ (l:B), P l le').
Proof.
  unfold_locally. red. intros. red in H2. eapply prop_eq.
  apply list_eq_comm. eauto. apply H2. intros. apply H0. apply H; auto.
Qed.

Lemma locally_exists' {A B} : forall P (le : t A),
      ⊢(∃ t, locally le (fun le' => P t le')) -∗ locally le (fun le' => ∃ (t : B), P t le').
Proof.
  unfold_locally. intros. clear H3. destruct H2. repeat red. exists x.
  eapply prop_eq. apply list_eq_comm. eauto. apply H2. intros. apply H0. apply H; auto.
Qed.

Lemma locally_exists {A B} : forall P (le : t A), ∀ t,
      ⊢locally le (fun le' => P t le') -∗ locally le (fun le' => ∃ (t : B), P t le').
Proof.
  iIntros. iApply locally_exists'. iExists t0. iFrame.
Qed.

Lemma locally_delete_2 {A} : forall P Q R (le : t A),
    ⊢locally le (fun le' => R le') -∗
     locally le (fun le' => P le') -∗
     (∀ le, R le -∗ P le -∗ Q le) -∗
     locally le (fun le' => Q le').
Proof.
  iIntros "* HA HB HC". iDestruct (locally_sep with "HA HB") as "HA".
  iApply (locally_consequence with "HA [HC]"). iIntros "* [HA HB]".
  iApply ("HC" with "HA HB").
Qed.

Lemma locally_delete_3 {A} : forall P Q R S (le : t A),
      ⊢locally le (fun le' => R le') -∗
      locally le (fun le' => P le') -∗
      locally le (fun le' => S le') -∗
      (∀ le, R le -∗ P le -∗ S le -∗ Q le) -∗
      locally le (fun le' => Q le').
Proof.
  iIntros "* HA HB HC HD". iDestruct (locally_sep with "HB HC") as "HB".
  iApply (locally_delete_2 with "HA HB"). iIntros "* HA [HB HC]". iApply ("HD" with "HA HB HC").
Qed.

Lemma locally_conseq {A} : forall P Q Q' (le : t A),
    ⊢locally le (fun le' => P le' -∗ Q le') -∗
    locally le (fun le' => Q le' -∗ Q' le') -∗
    locally le (fun le' => P le' -∗ Q' le').
Proof.
  iIntros "* HA HB". iApply (locally_delete_2 with "HA HB"). iIntros "* HA HB HC".
  iApply "HB". iApply "HA". iFrame.
Qed.

Lemma locally_frame_l {A} : forall P Q (le : t A),
    ⊢ P -∗ locally le (fun le' => Q le') -∗ locally le (fun le' => P ∗ Q le').
Proof.
  iIntros. iApply locally_sep_indep_l. iFrame.
Qed.

Lemma locally_frame_r {A} : forall P Q (le : t A),
    ⊢ P -∗ locally le (fun le' => Q le') -∗ locally le (fun le' => Q le' ∗ P).
Proof.
  iIntros. iApply locally_sep_indep_r. iFrame.
Qed.

Lemma locally_set {A} : forall Q (le : t A) t v,
    ⊢ IsFresh t -∗ locally le (fun le' => Q le') -∗ locally (set t v le) (fun le' => Q le') ∗ IsFresh t.
Proof.
  unfold_locally. red in H2. clear H3 H1. subst. repeat red. intros. destruct a. clear H0.
  exists (hheap_ctx h), h, nil. split; auto. repeat split; auto.
  split. split. intros l H0. inversion_star h P. clear H0. red in P0. exists h2, h0. split.
  intros le' P3. eapply P1. intros. erewrite <- P3. assert (id <> t0). intro. subst.
  eapply P2 in H0; eauto. apply P0. apply H. apply H2. apply in_eq. rewrite gso; auto. auto.
  split; auto. eapply list_eq_trans; eauto. eapply list_eq_trans; eauto.
  split. apply list_disjoint_comm; auto. apply list_eq_union_comm. auto.
  reflexivity. split. apply list_disjoint_empty_r. simpl_list. split; auto.
Qed.

Lemma locally_lookup {A} : forall le t (v : A),
    ⊢ IsFresh t -∗ locally (set t v le) (λ le', ⌜le' ! t = Some v⌝).
Proof.
  unfold_locally. intros. red. erewrite <- H0. apply gss. rewrite H. apply H2. apply in_eq.
Qed.

Lemma locally_out {A} : forall P Q (le : t A),
    ⊢locally le (fun le' => P le' -∗ Q le') -∗ P le -∗ Q le.
Proof.
  iIntros "* HA HB". iDestruct (locally_elim with "HA HB") as "HA". iApply "HA".
Qed.

Lemma locally_conseq_pure {A} : forall (P Q : t A -> Prop) (le : t A),
    (forall le, P le -> Q le) -> ⊢locally le (λ le', ⌜ P le' ⌝) -∗ locally le (λ le', ⌜ Q le' ⌝).
Proof.
  intros. iApply locally_consequence_2. eauto.
Qed.

Lemma locally_destruct {A} : forall Q (le : t A) P,
    ⊢locally le (fun le' => P ∗ Q le') -∗ locally le (fun le' => (P -∗ P ∗ Q le') ∗ P).
Proof.
  iIntros "* HA".
  iApply (locally_consequence with "HA"). iIntros "* [HA HB]". iSplitR "HA"; auto.
  iIntros "$ //".
Qed.
