Implicit Type X: Type.
(* =FreeFresh= *)
Inductive FreeFresh X :=
| ret : X -> FreeFresh X
| gensymOp : unit -> (nat -> FreeFresh X) -> FreeFresh X.
(* =end= *)

Arguments ret [X] _.
Arguments gensymOp [X] _ _.

(* =fresh= *)
Definition gensym (tt: unit): FreeFresh nat := gensymOp tt (@ret nat).
(* =end= *)

Section Bind.
Variable X Y: Type.
(* =bind= *)
Fixpoint bind (m: FreeFresh X)(f: X -> FreeFresh Y): FreeFresh Y :=
  match m with
  | ret v => f v
  | gensymOp _ k => gensymOp tt (fun n => bind (k n) f)
  end.
(* =end= *)
End Bind.

Arguments bind [_][_] m f.

Notation "'ret!' v" := (ret v) (at level 20).

Notation "'do' x '<-' e1 ';' e2" :=
  (bind e1 (fun x => e2)) (x name, at level 50).

Require Import tree.

(* =label= *)
Fixpoint label {X} (t : Tree X) : FreeFresh (Tree nat):=
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
