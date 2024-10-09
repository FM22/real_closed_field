/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.RealClosedField.FormallyReal
import RealClosedField.RealClosedField.RingOrdering.Field

/-
TODO: Over a [Field F]

1. RingPreordering is RingCone
2. RingOrdering is maximal RingCone
3. IsSemireal F → IsFormallyReal F
4. IsSemiReal F → construct LinearOrderedField
5. ordering exists on F ↔ IsSemireal F

TODO: think about how to maximise typeclass / instance use here

-/

variable (F S : Type*) [Field F] [SetLike S F]

instance RingPreorderingClass.instRingConeClass [RingPreorderingClass S F] : RingConeClass S F where
  eq_zero_of_mem_of_neg_mem {P} {a} ha hna := by
    by_contra h
    have : a⁻¹ * -a ∈ P := by aesop (config := { enableSimp := False })
    exact minus_one_not_mem P (by aesop)

instance RingOrderingClass.instIsMaxCone [RingOrderingClass S F] (O : S) : IsMaxCone O where
  mem_or_neg_mem := mem_or_neg_mem O

instance IsSemireal.instIsFormallyReal [IsSemireal F] : IsFormallyReal F := by
  refine IsFormallyReal.of_eq_zero_of_square_and_eq_zero_of_sum ?_ ?_
