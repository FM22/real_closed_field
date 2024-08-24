import RealClosedField.Mathlib.Algebra.Order.Ring.Cone
import RealClosedField.Mathlib.Algebra.Ring.Semireal.Defs

variable (R : Type*)

class IsFormallyReal [Add R] [Mul R] [Zero R] : Prop where
  not_nontrivial_isSumSq_eq_zero (a S : R) (hS : IsSumSq S) (is_zero : a * a + S = 0) : a = 0

export IsFormallyReal (not_nontrivial_isSumSq_eq_zero)

instance [MulZeroOneClass R] [Add R] [Nontrivial R] [IsFormallyReal R] :
    IsSemireal R where
  not_IsSumSq_neg_one a ssa amo :=
    one_ne_zero' R (not_nontrivial_isSumSq_eq_zero 1 a ssa (by simpa using amo))

instance [LinearOrderedRing R] : IsFormallyReal R where
  not_nontrivial_isSumSq_eq_zero a _ hS is_zero :=
    mul_self_eq_zero.mp (le_antisymm
      (le_of_eq_of_le (eq_neg_of_add_eq_zero_left is_zero)
                      (Right.neg_nonpos_iff.mpr (IsSumSq.nonneg hS)))
      (mul_self_nonneg a))

variable {R} in
theorem IsFormallyReal.no_nontrivial_add_isSumSq_eq_zero
    [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {S₁ S₂ : R} (hS₁ : IsSumSq S₁) (hS₂ : IsSumSq S₂) (hSum : S₁ + S₂ = 0) : S₁ = 0 := by
  induction hS₁
  case zero => rfl
  case sq_add a S hS ih =>
    have az : a = 0 :=
      not_nontrivial_isSumSq_eq_zero a (S + S₂) (IsSumSq.add hS hS₂)
                                      (by simpa [add_assoc] using hSum);
    have sz : S = 0 := ih (by simpa [az] using hSum);
    simp [az, sz]

theorem IsFormallyReal.equiv_def_2 [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] :
    IsFormallyReal R ↔ (∀ {S₁ S₂ : R}, IsSumSq S₁ → IsSumSq S₂ → S₁ + S₂ = 0 → S₁ = 0) := by
  apply Iff.intro
  case mp  => intro _; exact IsFormallyReal.no_nontrivial_add_isSumSq_eq_zero
  case mpr =>
    intro no_nontriv_sum; constructor; intros a S hS sum_zero;
    exact mul_self_eq_zero.mp (no_nontriv_sum (isSumSq_mul_self a) hS sum_zero)

theorem IsFormallyReal.equiv_def [AddCommMonoid R] [Mul R] :
  IsFormallyReal R ↔ (∀ S : Finset R, ∑ x ∈ S, x * x = 0 → ∀ x ∈ S, x = 0) := by
  apply Iff.intro
  case mp  => intros formReal S sum_eq_zero x x_mem_S; sorry
  case mpr => intro no_nontrivial_sum_squares; constructor; intro a S hS sum_zero; induction hS


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
    IsFormallyReal.no_nontrivial_add_isSumSq_eq_zero hx hnx (add_neg_cancel x)

@[simp] lemma sumSqIn_toSubsemiring : (sumSqIn T).toSubsemiring = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end RingConeWithSquares