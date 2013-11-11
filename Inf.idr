import Data.Vect

Onto : (a -> b) -> Type
Onto {a} {b} f = (y : b) -> (x : a ** f x = y)

ontoId : {a : Type} -> Onto (id {a})
ontoId = \y => (y ** refl)

inf : Type -> Type
inf a = (n : Nat) -> Not (f : (Fin n -> a) ** Onto f)

pi1 : {a : Type} -> {P : a -> Type} -> (x : a ** P x) -> a
pi1 (x ** _) = x

total
finZEmpty : Fin Z -> a
finZEmpty fZ impossible
finZEmpty (fS x) impossible


natInf : inf Nat
natInf Z (f ** onto) = finZEmpty hm where
  hm : Fin Z
  hm = pi1 (onto 1)

natInf (S n) (f ** onto) = ?idk

fins : (n : Nat) -> (xs : Vect n (Fin n) ** ((x : Fin n) -> Elem x xs))
fins Z     = ([] ** finZEmpty)
fins (S n) = ?hmm  where
  ih : (xs : Vect n (Fin n) ** ((x : Fin n) -> Elem x xs))
  ih = fins n
