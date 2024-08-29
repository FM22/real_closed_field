/-
paste into corresponding file
-/
import Mathlib.Algebra.Order.Ring.Basic

/-- Turn an ordered domain into a strict ordered ring. -/
def OrderedRing.toStrictOrderedRing (α : Type*) [OrderedRing α] [IsDomain α] :
    StrictOrderedRing α where
  __ := ‹OrderedRing α›
  __ := ‹IsDomain α›
  mul_pos a b ap bp := (mul_nonneg ap.le bp.le).lt_of_ne' (mul_ne_zero ap.ne' bp.ne')
