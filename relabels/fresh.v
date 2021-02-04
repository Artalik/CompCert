Require Import freefresh.

Section Eval.
Variable X: Type.

(* =eval= *)
Fixpoint eval (m: FreeFresh X): nat -> X * nat :=
  match m with
  | ret v => fun n => (v, n)
  | gensymOp _ k => fun n => eval (k n) (1 + n)
  end.
(* =end= *)

(* =run= *)
Definition run (m: FreeFresh X): X := fst (eval m 0).
(* =end= *)

End Eval.

Arguments eval [_] m.
Arguments run [_] m.

Require Import tree.

Section Relabel.

Variable X: Type.

(* =relabel= *)
Definition relabel (t: Tree X): Tree nat := run (label t).
(* =end= *)

End Relabel.

Arguments relabel [_] t.
