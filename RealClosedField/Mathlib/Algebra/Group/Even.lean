/-
Renamed lemma
-/

import Mathlib.Algebra.Group.Even

@[to_additive (attr := simp)] lemma IsSquare.mul_self [Mul α] (m : α) : IsSquare (m * m) := ⟨m, rfl⟩
