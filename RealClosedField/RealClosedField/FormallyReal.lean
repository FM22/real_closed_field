import RealClosedField.Mathlib.Algebra.Order.Ring.Cone
import RealClosedField.Mathlib.Algebra.Ring.Semireal.Defs

variable (R : Type*)

class IsFormallyReal [Add R] [Mul R] [One R] [Zero R] : Prop where
  not_nontrivial_isSumSq_eq_zero (a S : R) (hS : IsSumSq S) (is_zero : a * a + S = 0) : a = 0

export IsFormallyReal (not_nontrivial_isSumSq_eq_zero)

instance [MulZeroOneClass R] [Add R] [Nontrivial R] [IsFormallyReal R] :
    IsSemireal R where
  not_IsSumSq_neg_one a ssa amo :=
    one_ne_zero' R (by rw [← one_mul 1] at amo; exact not_nontrivial_isSumSq_eq_zero 1 a ssa amo)

instance [LinearOrderedRing R] : IsFormallyReal R where
  not_nontrivial_isSumSq_eq_zero a _ hS is_zero :=
    mul_self_eq_zero.mp (le_antisymm
      (le_of_eq_of_le (eq_neg_of_add_eq_zero_left is_zero)
                      (Right.neg_nonpos_iff.mpr (IsSumSq.nonneg hS)))
      (mul_self_nonneg a))

theorem IsFormallyReal.equiv_def [AddCommMonoid R] [Mul R] [One R] :
  IsFormallyReal R ↔ (∀ S : Finset R, ∑ x ∈ S, x * x = 0 → ∀ x ∈ S, x = 0) := sorry

theorem IsFormallyReal.equiv_def_2 [AddMonoid R] [Mul R] [One R] :
  IsFormallyReal R ↔ (∀ {S₁ S₂}, IsSumSq S₁ → IsSumSq S₂ → S₁ + S₂ = 0 → S₁ = 0) := sorry

def RingConeWithSquares.sumSqIn [CommRing R] [IsFormallyReal R] : RingConeWithSquares R where
  __ := Subsemiring.sumSqIn R
  square_mem' a := isSumSq_mul_self a
  eq_zero_of_mem_of_neg_mem' ha hna :=
    have := (IsFormallyReal.equiv_def_2 R).mpr ha hna
    sorry
