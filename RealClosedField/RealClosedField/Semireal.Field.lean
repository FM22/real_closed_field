/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.RealClosedField.FormallyReal
import RealClosedField.RealClosedField.RingOrdering.Field

variable (F S : Type*) [Field F] [SetLike S F]

instance RingPreorderingClass.instRingConeClass [RingPreorderingClass S F] : RingConeClass S F where
  eq_zero_of_mem_of_neg_mem {P} {a} ha hna := by
    by_contra h
    have : a⁻¹ * -a ∈ P := by aesop (config := { enableSimp := False })
    exact minus_one_not_mem P (by aesop)

instance RingOrderingClass.instIsMaxCone [RingOrderingClass S F] (O : S) : IsMaxCone O where
  mem_or_neg_mem := mem_or_neg_mem O

open Classical in
instance IsSemireal.instIsFormallyReal [IsSemireal F] : IsFormallyReal F where
  eq_zero_of_sum_of_squares_eq_zero {ι} {I} {x} {i} hx hi := by
    by_contra
    refine add_one_ne_zero_of_isSumSq (IsSumSq.mul (IsSumSq.sum_mul_self _) (IsSumSq.mul_self _))
      (by field_simp [hx] : 1 + (∑ j ∈ I.erase i, x j * x j) * ((x i)⁻¹ * (x i)⁻¹) = 0)

noncomputable def LinearOrderedField.mkOfIsSemireal [IsSemireal F] : LinearOrderedField F where
  __ := LinearOrderedRing.mkOfCone
          (Classical.choose <| RingPreordering.exists_le_ordering <| RingPreordering.sumSqIn F)
          (Classical.decPred _)
  __ := ‹Field F›

theorem ArtinSchreier_basic :
    Nonempty ({S : LinearOrderedField F // S.toField = ‹Field F›}) ↔ IsSemireal F := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rcases Classical.choice h with ⟨inst, extend⟩
    exact LinearOrderedSemiring.instIsSemireal F
  · exact Nonempty.intro ⟨LinearOrderedField.mkOfIsSemireal F, by aesop⟩
