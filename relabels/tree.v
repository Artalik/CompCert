(* =tree= *)
Inductive Tree (X: Type) :=
| Leaf: X -> Tree X
| Node: Tree X -> Tree X -> Tree X.
(* =end= *)

Arguments Leaf [X] _.
Arguments Node [X] _ _.
