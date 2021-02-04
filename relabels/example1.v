Require Import List Lia.
Require Import tree.

Implicit Type X Y : Type.

(* =state= *)
Definition Fresh X := nat -> X * nat.
(* =end= *)

Section Monad.
  Variable X Y : Type.
  Implicit Type x : X.
  Implicit Type m : Fresh X.
  Implicit Type f: X -> Fresh Y.

(* =state_monad= *)
Definition ret (x: X): Fresh X :=
  fun n => (x, n).
Definition bind (m: Fresh X)(f: X -> Fresh Y): Fresh Y :=
  fun n => let (x, n') := m n in f x n'.
Definition gensym (tt: unit): Fresh nat :=
  fun n => (n, 1+n).
(* =end= *)

End Monad.

Arguments ret [_] x.
Arguments bind [_][_] m f.

Notation "'do' x '<-' e1 ';' e2" :=
  (bind e1 (fun x => e2)) (x name, at level 50).

Notation "'ret!' v ":= (ret v) (at level 50, left associativity).

(* =label= *)
Fixpoint label {X} (t: Tree X): Fresh (Tree nat) :=
  match t with
  | Leaf _ =>
    do n <- gensym tt;
    ret! (Leaf n)
  | Node l r =>
    do l <- label l;
    do r <- label r;
    ret! (Node l r)
  end.
(* =end= *)

Definition interval a b := seq a (1 + b - a).

Fixpoint flatten {X} (t : Tree X) : list X :=
  match t with
  | Leaf e => e :: nil
  | Node l r => flatten l ++ flatten r
  end.

Section Bind_Inversion.
Variable X Y : Type.
Implicit Type m: Fresh X.
Implicit Type f: X -> Fresh Y.
Implicit Type y: Y.
Implicit Type n: nat.

(* =bind_inversion= *)
Remark bind_inversion: forall m f y n1 n3,
    (do x <- m; f x) n1 = (y, n3) ->
    exists v n2, m n1 = (v, n2) /\ f v n2 = (y, n3).
(* =end= *)
Proof.
  intros until n3. unfold bind. destruct (m n1). eauto.
Qed.

End Bind_Inversion.

Ltac monadInv H :=
  match type of H with
  | ((_,_) = (_,_)) => inversion H; clear H; try subst
  | (ret _ _ = (_,_)) =>
    inversion H; clear H; try subst
  | (gensym _ _ = (_,_)) =>
    unfold gensym in H; inversion H; clear H; try subst
  | (bind ?F ?G ?Z = (?X,?Z')) =>
    let x := fresh "x" in
    let z := fresh "z" in
    let I1 := fresh "I" in
    let I2 := fresh "I" in
    destruct (bind_inversion _ _ F G X Z Z' H) as [x [z [I1 I2]]];
    clear H;
    try (monadInv I1);
    try (monadInv I2)
  | (?F _ _ = (_,_)) =>
    ((progress simpl in H) || unfold F in H); monadInv H
  end.

Implicit Type ft: Tree nat.

Section LabelSpec.
Variable X: Type.
Implicit Type t: Tree X.


(* =label_spec= *)
Lemma label_spec : forall t n ft n',
    label t n = (ft, n') -> n < n' /\ flatten ft = interval n (n'-1).
(* =end= *)
Proof.
  induction t; intros.
  - apply bind_inversion in H as [t1' [n2 [Fresh Ret]]]. inversion Fresh. inversion Ret. subst.
    split. lia. simpl. unfold interval. rewrite PeanoNat.Nat.sub_0_r.
    rewrite PeanoNat.Nat.sub_succ_l; auto. rewrite <- Minus.minus_diag_reverse. auto.
  - simpl in H. apply bind_inversion in H as [t1' [n2 [Label1 EQ]]].
    apply bind_inversion in EQ as [t2' [n3 [Label2 EQ]]]. inversion EQ. subst.
    apply IHt1 in Label1 as [P0 P1]. apply IHt2 in Label2 as [P2 P3]. split. lia. simpl.
    rewrite P1,P3. unfold interval.
    assert (n + (1 + (n2 - 1) - n) = n2) by lia.
    epose (seq_app (1 + (n2 - 1) - n) (1 + (n' - 1) - n2) n).
    rewrite H in e. rewrite <- e. f_equal. lia.
Qed.

End LabelSpec.

Lemma NoDupTree : forall n ft n', flatten ft = interval n n' -> NoDup (flatten ft).
Proof.
  intros n t n' P1.
  rewrite P1. unfold interval. apply seq_NoDup.
Qed.

Section Relabel.

Variable X: Type.
Implicit Type t: Tree X.

(* =relabel= *)
Definition relabel (t: Tree X): Tree nat := fst (label t 0).
(* =end= *)

(* =relabel_spec= *)
Lemma relabel_spec : forall t ft, relabel t = ft -> NoDup (flatten ft).
(* =end= *)
Proof.
intros.
eapply NoDupTree.
eapply label_spec.
unfold relabel in H.
rewrite <-H.
eapply surjective_pairing.
Qed.

End Relabel.
