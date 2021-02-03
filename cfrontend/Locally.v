Require Import MoSel.
Import weakestpre_gensym.
Export Maps.PTree.

Notation "a ! b" := (get b a) (at level 1).

Definition hlocally {A} (le : t A) (f : t A -> iProp) : hprop :=
  fun h => forall le', (forall id, id ∈ h -> le ! id = le' ! id) -> f le' () h.

Definition locally {A} (le : t A) (f : t A -> iProp) : iProp := MonPred (fun _ => hlocally le f) _.


(** Useful invariance properties. *)
Ltac inv H := inversion H; clear H; subst.

Ltac unfold_locally :=
unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
    destruct i; inv H; repeat red; intros a b; destruct a; clear b;
      exists emp; eexists; eexists; repeat split; auto;
        [intros h H0; inversion_star h H; clear H0; inversion H1; subst;
         simpl in *; rewrite union_empty_l_L
        | apply disjoint_empty_l | rewrite union_empty_l_L; auto ].

Lemma locally_base {A} : forall (le : t A), ⊢ locally le (fun le' => emp).
Proof.
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H.
  intros. inv H. reflexivity.
Qed.

Lemma locally_elim {A} : forall P (le : t A), ⊢ locally le (fun le' => P le') -∗ P le.
Proof.
  unfold_locally. apply H2. intros. auto.
Qed.

Lemma locally_consequence {A} : forall (P Q : t A -> iProp) (le : t A),
    ⊢locally le (λ le', P le') -∗ (∀ le, P le -∗ Q le) -∗ locally le (λ le', Q le').
Proof.
  unfold_locally. clear H3. intros j P0. destruct j. clear P0.
  repeat red. exists (set_ctx h1), h1, ∅. repeat split; auto.
  red. intros. inversion_star h P. clear H. red in P1. subst.
  edestruct P2. reflexivity. inversion_star h P.
  clear H. destruct P4. inv H3. clear P5. rewrite union_empty_r_L.
  rewrite union_empty_r_L in P3 P2 H0. apply H.
  exists h, h1. repeat split; auto. apply H2. intros. eapply H0. apply elem_of_union_l.
  auto. rewrite union_comm_L. auto.
  apply disjoint_empty_r. rewrite union_empty_r_L. auto.
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
  exists (set_ctx h1), h1. eexists. repeat split; auto.
  repeat red. intros. inversion_star h P. clear H. red in P1. subst.
  exists h1, h0. repeat split; auto. apply H2.
  intros. eapply H0. apply elem_of_union_l. auto.
  apply P2. intros. eapply H0. apply elem_of_union_r. auto.
  apply disjoint_empty_r. rewrite union_empty_r_L. auto.
Qed.

Lemma locally_and {A} : forall P R (le : t A),
    ⊢locally le (fun le' => P le') ∧ locally le (fun le' => R le') -∗
            locally le (fun le' => P le' ∧ R le').
Proof.
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
  destruct i; inversion H as (H0); clear H; subst. intros j H; destruct j; clear H.
  exists emp; eexists; eexists; repeat split; auto.
  4 : rewrite union_empty_l_L; auto.
  3 : apply disjoint_empty_l.
  1-2 :inversion_star h P; clear H; destruct P2; inv P1; clear P3; simpl in *;
    rewrite union_empty_l_L; rewrite union_empty_l_L in H0.
  apply H. intros. eapply H0. eauto.
  apply H1. intros. eapply H0. eauto.
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
  unfold_locally. clear H3. red in H2. inversion_star h P. clear H2. intros.
  exists h, h0. repeat split; auto. apply P2. intros. eapply H. rewrite P0.
  apply elem_of_union_r. auto.
Qed.

Lemma locally_idempotence {A} : forall P (le : t A),
    ⊢locally le (fun le' => P le') -∗ locally le (fun le' => locally le' (fun le'' => P le'')).
Proof.
  unfold_locally. intros. eapply H2. intros. erewrite H; eauto.
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
  unfold_locally. red. intros. apply H2. auto.
Qed.

Lemma locally_exists' {A B} : forall P (le : t A),
      ⊢(∃ t, locally le (fun le' => P t le')) -∗ locally le (fun le' => ∃ (t : B), P t le').
Proof.
  unfold_locally. intros. clear H3. destruct H2. repeat red. exists x. apply H0; auto.
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
    ⊢ & t -∗ locally le (fun le' => Q le') -∗ locally (set t v le) (fun le' => Q le') ∗ & t.
Proof.
  unfold_locally. red in H2. clear H3 H1. subst. repeat red. intros. destruct a. clear H.
  exists (hsingle t0). do 2 eexists. split; auto. reflexivity. repeat split; auto.
  intros h P. inversion_star h P. clear P. red in P1. subst. exists h1. eexists. split.
  intros le' P4. eapply P2. intros. erewrite <- P4. assert (id <> t0). intro. subst.
  eapply P3; eauto. apply lookup_singleton.
  rewrite gso; eauto. eauto.
  repeat split; auto. rewrite union_comm_L; auto.
  apply disjoint_empty_r.
  rewrite union_empty_r_L. eauto.
Qed.

Lemma locally_lookup {A} : forall le t (v : A),
    ⊢ & t -∗ locally (set t v le) (λ le', ⌜le' ! t = Some v⌝).
Proof.
  unfold_locally. intros. red. erewrite <- H. apply gss. rewrite H2.
  apply lookup_singleton.
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
