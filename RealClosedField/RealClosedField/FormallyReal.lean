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
  IsFormallyReal R ↔ (∀ {S₁ S₂ : R}, IsSumSq S₁ → IsSumSq S₂ → S₁ + S₂ = 0 → S₁ = 0) := sorry

namespace RingConeWithSquares
variable {T : Type*} [CommRing T] [IsFormallyReal T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : RingConeWithSquares T where
  __ := Subsemiring.sumSqIn T
  square_mem' x := isSumSq_mul_self x
  eq_zero_of_mem_of_neg_mem' {x} hx hnx :=
    (IsFormallyReal.equiv_def_2 T).mp ‹IsFormallyReal T› hx hnx (add_neg_cancel x)

@[simp] lemma sumSqIn_toSubsemiring : (sumSqIn T).toSubsemiring = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end RingConeWithSquares
