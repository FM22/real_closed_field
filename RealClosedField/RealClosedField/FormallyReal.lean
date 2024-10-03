import Mathlib.Algebra.Order.Ring.Cone
import RealClosedField.Mathlib.Algebra.Ring.Semireal.Defs

class IsFormallyReal (R : Type*) [AddCommMonoid R] [Mul R] : Prop where
  eq_zero_of_sum_of_squares_eq_zero {ι : Type} {I : Finset ι} {x : ι → R} {i : ι}
    (hx : ∑ i ∈ I, x i * x i = 0) (hi : i ∈ I) : x i = 0

export IsFormallyReal (eq_zero_of_sum_of_squares_eq_zero)

/- Universe polymorphic version of `IsFormallyReal.eq_zero_of_sum_of_squares_eq_zero` -/
theorem IsFormallyReal.eq_zero_of_sum_of_squares_eq_zero' {R : Type*}
    [AddCommMonoid R] [Mul R] [IsFormallyReal R] {ι : Type*} {I : Finset ι} {x : ι → R} {i : ι}
    (hx : ∑ i ∈ I, x i * x i = 0) (hi : i ∈ I) : x i = 0 := by
  let xsq := (fun i => x i * x i)
  have : ∑ x : Fin I.card, xsq ↑(I.equivFin.symm x) = 0 :=
    by simpa [Finset.sum_attach, hx]
    using Fintype.sum_equiv (I.equivFin.symm) (xsq <| I.equivFin.symm ·) (xsq ·) (by simp)
  simpa using eq_zero_of_sum_of_squares_eq_zero this (by simp : I.equivFin ⟨i, hi⟩ ∈ _)

theorem IsFormallyReal.eq_zero_of_square_eq_zero {R : Type*}
    [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} (h : a * a = 0) : a = 0 := by
  exact eq_zero_of_sum_of_squares_eq_zero
    (by simpa : ∑ i : Option Empty, a * a = 0) (by simp : default ∈ _)

theorem IsFormallyReal.eq_zero_of_isSumSq_of_sum_eq_zero {R : Type*}
    [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {S₁ S₂ : R}
    (hS₁ : IsSumSq S₁) (hS₂ : IsSumSq S₂) : S₁ + S₂ = 0 → S₁ = 0 := by
  rw [isSumSq_iff_exists_sum] at *
  obtain ⟨ι, I, x, rfl⟩ := hS₁; obtain ⟨β, J, y, rfl⟩ := hS₂
  intro h
  suffices ∀ i ∈ I, x i = 0
    by simpa using Finset.sum_eq_zero (f := fun i => x i * x i) (by simp [this · ·])
  have : ∑ i ∈ I.disjSum J, Sum.elim x y i * Sum.elim x y i = 0 := by simpa
  exact fun i _ => eq_zero_of_sum_of_squares_eq_zero this (i := Sum.inl i) (by simpa)

theorem IsFormallyReal.eq_zero_of_isSumSq_of_sum_eq_zero' {R : Type*}
    [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {S₁ S₂ : R}
    (hS₁ : IsSumSq S₁) (hS₂ : IsSumSq S₂) (h : S₁ + S₂ = 0): S₂ = 0 := by
  simp_all [eq_zero_of_isSumSq_of_sum_eq_zero hS₁ hS₂ h]

open Classical in
theorem IsFormallyReal.of_eq_zero_of_square_and_eq_zero_of_sum (R : Type*) [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (hs : ∀ {S₁ S₂ : R}, IsSumSq S₁ → IsSumSq S₂ → S₁ + S₂ = 0 → S₁ = 0) : IsFormallyReal R where
  eq_zero_of_sum_of_squares_eq_zero {_} {I} {x} {i} hx hi :=
    hz (hs (S₂ := ∑ j ∈ I.erase i, x j * x j) (by aesop) (by aesop)
        (by simpa [hx] using Finset.add_sum_erase _ (fun j => x j * x j) hi))

instance [NonAssocSemiring R] [Nontrivial R] [IsFormallyReal R] : IsSemireal R where
  add_one_ne_zero_of_isSumSq hS h_contr := by
    simpa using IsFormallyReal.eq_zero_of_isSumSq_of_sum_eq_zero (by aesop) hS h_contr

open Classical in
instance [LinearOrderedRing R] : IsFormallyReal R where
  eq_zero_of_sum_of_squares_eq_zero {ι} {I} {x} {i} hx hi := by
    rw [← Finset.add_sum_erase _ _ hi] at hx
    exact mul_self_eq_zero.mp (le_antisymm
      (by simpa [eq_neg_of_add_eq_zero_left hx] using Finset.sum_nonneg (by simp [mul_self_nonneg]))
      (mul_self_nonneg <| x i))

namespace RingCone
variable {T : Type*} [CommRing T] [IsFormallyReal T] {a : T}

variable (T) in
/--
In a formally real commutative ring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : RingCone T where
  __ := Subsemiring.sumSqIn T
  eq_zero_of_mem_of_neg_mem' {x} hx hnx :=
    IsFormallyReal.eq_zero_of_isSumSq_of_sum_eq_zero hx hnx (add_neg_cancel x)

@[simp] lemma sumSqIn_toSubsemiring : (sumSqIn T).toSubsemiring = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end RingCone
