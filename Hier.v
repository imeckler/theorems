Require Import Overture PathGroupoids Equivalences Trunc HSet.
Require Import types.Paths types.Forall types.Arrow types.Universe types.Empty types.Unit.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

Local Inductive V : Type :=
  | set : forall (A : Type), (A -> V) -> V
  | x : V.

Axiom surjpath : forall (A B : Type),
                 forall (f : A -> V) (g : B -> V),
                 (forall (a : A), exists (b : B), f a = g b) ->
                 (forall (b : B), exists (a : A), f a = g b) ->
                 (set A f) = (set B g).

Axiom hiertrunc : forall (x y : V) (p q : x = y), p = q.


Definition member : (x : V) -> (v : V) -> Type := fun x v =>
  match v with
  | _ => 2.

 (* exists (a : A), x = f a.*)
 
  (*match v with
       (set A f) -> exists (a : A), x = f a.*)
