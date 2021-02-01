From iris.proofmode Require Export base intro_patterns spec_patterns
     sel_patterns coq_tactics reduction
     coq_tactics ltac_tactics.
Require Import FunctionalExtensionality.
From iris Require Export bi.bi proofmode.tactics proofmode.monpred proofmode.reduction.
From stdpp Require Export pmap.
Require Import SepList.

Global Set Warnings "-convert_concl_no_check".

Module SepBasicCore.

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

  Local Ltac Fresh :=
    let x := iFresh in
    match x with
    | IAnon ?x =>
      let x := eval compute in (ascii_of_pos (x + 64)) in
          let x := eval compute in (append "H" (string_of_list_ascii [x])) in
              let env := iGetCtx in
              let P := reduction.pm_eval (envs_lookup x env) in
              match P with
              | None => x
              | Some _ => Fresh
              end
    | _ => fail "iFresh returns " x " sometimes."
    end.

  (*h should be in the environment *)
  Local Ltac norm h :=
    let env := iGetCtx in
    let P := reduction.pm_eval (envs_lookup h env) in
    match P with
    | None => fail "assert false"
    | Some (false, ?P) =>
      match P with
      | bi_exist ?Q => let x := fresh "x" in (iDestruct h as (x) h; norm h)
      | bi_sep ?Q ?W =>
        let x := Fresh in
        let y := Fresh in
        eapply tac_and_destruct with h _ x y _ _ _;
        [ pm_reflexivity | pm_reduce; iSolveTC | pm_reduce; norm x; norm y]
      | bi_pure (and ?P ?Q) =>
        let x := Fresh in
        eapply tac_and_destruct with h _ h x _ _ _;
        [pm_reflexivity
        |pm_reduce; iSolveTC
        |pm_reduce; norm h; norm x]
      | bi_pure _ => iPure h as ?
      | bi_wand _ _ => iDestruct (h with "[]") as h; [progress auto | norm h]
      | bi_absorbingly _ =>
        let name := Fresh in
        let name_mod := eval compute in (append ">" name) in
            iPoseProof h as name; iDestruct name as name_mod; norm name
      | _ =>
        match h with
        | IAnon _ =>
          let x := Fresh in
          iPoseProof h as x
        | _ => idtac
        end
      end
    | Some (true,?P) => idtac
    end.

  (* (List.fold norm) in Ltac *)
  Local Ltac norm_list l :=
    match l with
    | [] => idtac
    | ?h :: ?t => norm h ; norm_list t
    end.


  Ltac norm_all :=
    iStartProof;
    let env := iGetCtx in
    let list_ident := eval compute in (rev (envs_dom env)) in
        norm_list list_ident; auto.

  Tactic Notation "iNorm" := norm_all.

End SepBasicCore.

Require Import Ctypes.

Module gensym.
  Import Errors.
  Export SepBasicCore.
  Export SepList.

  Definition ident := positive.

  Record generator : Type := mkgenerator { gen_next : ident;
                                           gen_trail: list (ident * type)
                                         }.

  Definition initial_state : generator := mkgenerator 1%positive nil.


  Inductive mon (X : Type) : Type :=
  | ret : X -> mon X
  | errorOp : Errors.errmsg -> mon X
  | gensymOp : type -> (ident -> mon X) -> mon X
  | trailOp : unit -> (list (ident * type) -> mon X) -> mon X.

  Arguments errorOp [X].
  Arguments gensymOp [X].
  Arguments trailOp [X].
  Arguments ret {_} x.


  Fixpoint bind {X Y} (m : mon X) (f : X -> mon Y) : mon Y :=
    match m with
    | ret x => f x
    | errorOp e => errorOp e
    | gensymOp t g => gensymOp t (fun x => bind (g x) f)
    | trailOp _ g => trailOp tt (fun x => bind (g x) f)
    end.

  Notation "'let!' x ':=' e1 'in' e2" := (bind e1 (fun x => e2)) (x ident, at level 90).

  Notation "'ret!' v" := (ret v) (v ident, at level 90).

  Definition error {X} (e : Errors.errmsg) : mon X := errorOp e.
  Definition gensym (t : type) : mon ident := gensymOp t ret.
  Definition trail (_ : unit): mon (list (ident * type)) := trailOp tt ret.

  Lemma lid : forall X Y (a : X) (f : X -> mon Y), bind (ret a) f = f a.
  Proof. auto. Qed.

  Lemma rid : forall X (m : mon X), bind m ret = m.
  Proof.
    fix m 2.
    destruct m0.
    1 - 2 : reflexivity.
    all : simpl; do 2 f_equal.
    2 : destruct u; auto.
    all : apply functional_extensionality; intro; apply m.
  Qed.

  Lemma ass_bind : forall X Y Z (m : mon X) f (g : Y -> mon Z),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    fix m 4.
    destruct m0; intros.
    1 - 2 : reflexivity.
    all : simpl; do 2 f_equal; apply functional_extensionality; intro; apply m.
  Qed.

  Fixpoint eval {X} (m : mon X) : generator -> res (generator * X) :=
  match m with
  | ret v => fun s => OK (s, v)
  | errorOp e => fun s => Error e
  | gensymOp ty f =>
    fun s =>
      let h := gen_trail s in
      let n := gen_next s in
      eval (f n) (mkgenerator (Pos.succ n) ((n,ty) :: h))
  | trailOp _ f =>
    fun s =>
      let h := gen_trail s in
      eval (f h) s
  end.

Definition run {X} (m: mon X): res X :=
  match eval m initial_state with
  | OK (_, v) => OK v
  | Error e => Error e
  end.

End gensym.

Module weakestpre_gensym.
  Export gensym.
  Export proofmode.monpred.
  Export SepBasicCore.
  Import reduction.

  Definition iProp := monPred biInd (@hpropList ident).

  Fixpoint wp {X} (e1 : mon X) (Q : X -> iProp) : iProp :=
    match e1 with
    | ret v => Q v
    | errorOp e => True
    | gensymOp _ f => ∀ l, IsFresh l -∗ wp (f l) Q
    | trailOp _ f => ∀ l, wp (f l) Q
    end.

  Notation "'{{' P } } e {{ v ; Q } }" := (P -∗ wp e (fun v => Q))
                                            (at level 20,
                                             format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").

(** triple rules *)

Lemma wp_bind {X Y} (e : mon X) (f :  X → mon Y) (Q : Y -> iProp)  (Q' : X -> iProp) :
  wp e Q' ⊢ (∀ v,  Q' v -∗ wp (f v) Q ) -∗ wp (bind e f) Q %I.
Proof.
  iIntros "HA HB". revert e. fix e 1.
  destruct e0.
  - iApply "HB". iApply "HA".
  - simpl. auto.
  - simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA". iPoseProof "HB" as "HB". apply e.
  - simpl. iIntros (l). iDestruct ("HA" $! l) as "HA". iPoseProof "HB" as "HB". apply e.
Qed.

Lemma wp_consequence : forall {X} (P Q : X -> iProp) (f : mon X),
    ⊢ wp f P -∗
      (∀ x, P x -∗ Q x) -∗
      wp f Q.
Proof.
  induction f; simpl; intros; auto.
  - iIntros "HA HB". iApply ("HB" with "HA").
  - iIntros "HA * HB * HC". iApply (H with "[HA HC] HB"). iApply ("HA" with "HC").
  - iIntros "HA HB *". iApply (H with "HA HB").
Qed.

Lemma ret_spec {X} (v : X) H (Q : X -> iProp) :
  (H ⊢ Q v) -> ⊢{{ H }} ret v {{ v'; Q v' }}.
Proof. simpl; iIntros. iApply H0; auto. Qed.

Lemma bind_spec {X Y} (e : mon X) (f : X -> mon Y) Q Q' H :
   (⊢{{ H }} e {{ v; Q' v }}) ->
    (∀ v, ⊢{{ Q' v }} (f v) {{ v'; Q v' }}) ->
    ⊢ {{ H }} (bind e f) {{ v; Q v}}.
Proof.
  intros. iIntros "HA".
  iApply (wp_bind e f _ Q' with "[HA]").
  - iApply (H0 with "[HA]"); auto.
  - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.
Qed.

Lemma consequence {X} H H' (Q : X -> iProp) (Q' : X -> iProp) (e : mon X) :
  (⊢{{ H' }} e {{ v; Q' v }}) ->
  (forall v, Q' v ⊢ Q v) ->
  (H ⊢ H') ->
  ⊢{{ H }} e {{ v; Q v }}.
Proof.
  intros. iIntros "HA". iDestruct (H2 with "HA") as "HA".
  iDestruct (H0 with "HA") as "HA". iApply (wp_consequence with "HA"). iIntros "*". iApply H1.
Qed.


Lemma frame_bind : forall (P : iProp), ⊢ P -∗ emp ∗ P.
Proof. iIntros "* $". Qed.

Lemma frame {X} H R Q (e : mon X) :
  (⊢{{ H }} e {{ v; Q v }}) ->
  ⊢{{ H ∗ R }} e {{ v; Q v ∗ R }}.
Proof.
  intro P. iIntros "[HA HC]". iApply (wp_consequence with "[HA]").
  iApply P; auto. iIntros; iFrame.
Qed.

Lemma intro_true_r {X} H Q (e : mon X) :
  (⊢{{ emp ∗ H }} e {{ v; Q v }}) ->
  ⊢{{ H }} e {{ v; Q v }}.
Proof.
  intro P. iIntros "HA". iApply (P with "[HA]").
  iFrame.
Qed.

Lemma exists_spec {X Y} v' H (Q : X -> Y -> iProp) (e : mon X) :
  (⊢{{ H }} e {{ v; Q v v' }}) ->
  ⊢{{ H }} e {{ v; ∃ t, Q v t }}.
Proof.
  intros. iIntros "HA". iApply consequence; eauto.
Qed.

Ltac Frame := eapply intro_true_r; eapply frame.

(** Effects rules *)
Lemma gensym_spec ty :
  ⊢{{ emp }} gensym ty {{ l; IsFresh l }}.
Proof. simpl; auto. Qed.

Lemma error_spec {X} (Q : X -> iProp) e :
  ⊢{{ True }} error e {{ v; Q v }}.
Proof. auto. Qed.

Lemma trail_spec  : ⊢{{ emp }} trail tt {{ _; emp  }}.
Proof. auto. Qed.

End weakestpre_gensym.

Module adequacy.
  Import Errors.
  Export weakestpre_gensym.

  Definition inject n := List.map Pos.of_nat (seq 1 (pred (Pos.to_nat n))).

  Lemma inject_last : forall n, inject (Pos.succ n) = inject n ++ [n].
  Proof.
    intros. unfold inject. rewrite Pos2Nat.inj_succ. rewrite <- pred_Sn.
    rewrite <- (Pos2Nat.id n).
    assert (forall (n : nat), [Pos.of_nat n] = Pos.of_nat n :: map Pos.of_nat nil) by auto.
    rewrite H. rewrite <- map_cons. rewrite <- map_app. f_equal.
    rewrite Pos2Nat.id. assert (forall (n : nat), [n] = seq n 1) by auto. rewrite H0.
    assert (forall (n : nat), n > 0 ->1 + (Init.Nat.pred n) = n). intros. lia.
    pose (Pos2Nat.is_pos n). apply H1 in l.
    rewrite <- l. rewrite <- seq_app. f_equal. lia.
  Qed.

  Lemma next_disjoint : forall n, list_disjoint (inject n) [n].
  Proof.
    intros n x y P0 P1 eq. subst. inversion P1. subst.
    - unfold inject in P0. apply Coqlib.list_in_map_inv in P0. destruct P0 as [x [P0 P2]].
      apply in_seq in P2. destruct P2. lia.
    - inversion H.
  Qed.

  Lemma adequacy_wp {X} : forall (e : mon X) (Q : X -> iProp) (s s' : generator) v,
      (heap_ctx (inject (gen_next s)) ⊢ wp e Q) ->
      eval e s = Errors.OK (s', v) ->
      (Q v) () (inject (gen_next s')).
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H0; subst. apply soundness. iApply H.
    - inversion H0.
    - simpl in *. eapply e.
      2 : apply H0.
      + iIntros "HA". simpl. rewrite inject_last.
        iDestruct (heap_ctx_split with "HA") as "[HA HB]". apply next_disjoint.
        iDestruct (H with "HA") as "HA".
        iApply ("HA" with "HB").
    - simpl in *. eapply e; eauto. iIntros "HA". iApply (H with "HA").
  Qed.

  Lemma adequacy_init {X} : forall (e : mon X) (Q : X -> iProp) s' v,
      (⊢ wp e Q) ->
      eval e initial_state = Errors.OK (s', v) ->
      (Q v) () (inject (gen_next s')).
  Proof. intros. eapply adequacy_wp; eauto. auto. Qed.

  Lemma adequacy_core {X} : forall (e : mon X) (Q : X -> iProp) s v s' H,
      (heap_ctx (inject (gen_next s)) ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      eval e s = Errors.OK (s', v) ->
      (Q v) () (inject (gen_next s')).
  Proof.
    intros. eapply adequacy_wp; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA"); auto.
  Qed.

  Lemma adequacy_triple_init {X} : forall (e : mon X) (Q : X -> iProp) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      eval e initial_state = Errors.OK (s', v) ->
      (Q v) () (inject (gen_next s')).
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma adequacy_wp_pure {X} : forall (e : mon X) (Q : X -> Prop) s v s',
      (heap_ctx (inject (gen_next s)) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      eval e s = Errors.OK (s', v) ->
      Q v.
  Proof.
    intros. apply (soundness_pure (inject (gen_next s'))). iApply completeness.
    eapply (adequacy_wp _ _ _ _ _ H H0).
  Qed.

  Lemma adequacy_pure {X} : forall (e : mon X) (Q : X -> Prop) s v s' H,
      (heap_ctx (inject (gen_next s)) ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      eval e s = Errors.OK (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iDestruct (H1 with "HA") as "$".
  Qed.

  Section Adequacy.
  Variable X: Type.
  Implicit Type m: mon X.
  Implicit Type P: iProp.
  Implicit Type Q: X -> Prop.
  Implicit Type v: X.

  Lemma adequacy: forall m Q v,
      (⊢ {{ emp }} m {{ v; ⌜ Q v ⌝}}) ->
      run m = OK v -> Q v.
  Proof.
    intros m.
    unfold run. intros.
    destruct (eval m initial_state) eqn:H2.
    destruct p. inversion H0. subst.
    eapply adequacy_pure; eauto.
    iIntros "_".
    iApply H. auto.
    inversion H0.
  Qed.

  End Adequacy.

End adequacy.
