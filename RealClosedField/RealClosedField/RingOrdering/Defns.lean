/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.RingTheory.Ideal.Basic

/-!
## Preorderings
-/

section defns

variable (S R : Type*) [CommRing R] [SetLike S R]

/-- `RingPreorderingClass S R` says that `S` is a type of (ring) preorderings on `R`. -/
class RingPreorderingClass extends SubsemiringClass S R : Prop where
  square_mem (P : S) (x : R) : x * x ∈ P
  minus_one_not_mem (P : S) : -1 ∉ P

export RingPreorderingClass (square_mem)
export RingPreorderingClass (minus_one_not_mem)

attribute [aesop safe 0 apply (rule_sets := [SetLike])] square_mem

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
structure RingPreordering extends Subsemiring R where
  square_mem' (x : R) : x * x ∈ carrier
  minus_one_not_mem' : -1 ∉ carrier

instance RingPreordering.instSetLike : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance RingPreordering.instRingPreorderingClass : RingPreorderingClass (RingPreordering R) R where
  zero_mem {P} := P.zero_mem'
  one_mem {P} := P.one_mem'
  add_mem {P} := P.add_mem'
  mul_mem {P} := P.mul_mem'
  square_mem {P} := P.square_mem'
  minus_one_not_mem {P} := P.minus_one_not_mem'

@[simp]
theorem RingPreordering.mem_toSubsemiring {P : RingPreordering R} {x : R} :
  x ∈ P.toSubsemiring ↔ x ∈ P := Iff.rfl

@[simp]
theorem RingPreordering.coe_toSubsemiring {P : RingPreordering R} :
    (P.toSubsemiring : Set R) = P := rfl

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] (P : S)

def RingPreorderingClass.toRingPreordering : RingPreordering R where
  carrier := P
  zero_mem' := zero_mem P
  one_mem' := one_mem P
  add_mem' := add_mem
  mul_mem' := mul_mem
  square_mem' := square_mem P
  minus_one_not_mem' := minus_one_not_mem P

@[simp]
lemma RingPreorderingClass.mem_toRingPreordering {x : R} :
    x ∈ (toRingPreordering P : Set R) ↔  x ∈ P := by
  rw [toRingPreordering]; aesop

@[simp]
lemma RingPreorderingClass.coe_toRingPreordering : (toRingPreordering P : Set R) = P := by
  rw [toRingPreordering]; rfl

end defns

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] {P : S}

/-!
## Support
-/

namespace RingPreordering.AddSubgroup

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : AddSubgroup R where
  carrier := {x : R | x ∈ P ∧ -x ∈ P}
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

@[simp] lemma mem_support : x ∈ support P ↔ x ∈ P ∧ -x ∈ P := Iff.rfl
@[simp, norm_cast] lemma coe_support : support P = {x : R | x ∈ P ∧ -x ∈ P} := rfl

end AddSubgroup

variable (P) in
class HasIdealSupport : Prop where
  smul_mem_support' (x : R) {a : R} (ha : a ∈ AddSubgroup.support P) :
    x * a ∈ AddSubgroup.support P

variable (P) in
/-- Technical lemma to get P as explicit argument -/
lemma smul_mem_support [HasIdealSupport P] :
    ∀ (x : R) {a : R}, a ∈ AddSubgroup.support P →
      x * a ∈ AddSubgroup.support P :=
  HasIdealSupport.smul_mem_support' (P := P)

theorem hasIdealSupport
    (h : ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P) : HasIdealSupport P where
  smul_mem_support' := by simp_all

namespace Ideal

variable [HasIdealSupport P]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := AddSubgroup.support P
  smul_mem' := by simpa using smul_mem_support P

@[simp] lemma mem_support : x ∈ support P ↔ x ∈ P ∧ -x ∈ P := Iff.rfl
@[simp, norm_cast] lemma coe_support : support P = {x : R | x ∈ P ∧ -x ∈ P} := rfl

end Ideal

/-!
## (Prime) orderings
-/

section IsOrdering

variable (P) in
/-- An ordering `P` on a ring `R` is a preordering such that, for every `x` in `R`,
either `x` or `-x` lies in `P`. -/
class IsOrdering : Prop where
  mem_or_neg_mem' (x : R) : x ∈ P ∨ -x ∈ P

variable [IsOrdering P]

variable (P) in
/-- Technical lemma to get P as explicit argument -/
lemma mem_or_neg_mem : ∀ x : R, x ∈ P ∨ -x ∈ P := IsOrdering.mem_or_neg_mem' (P := P)

end IsOrdering

variable (P) in
/-- A prime ordering `P` on a ring `R` is an ordering whose support is a prime ideal. -/
class IsPrimeOrdering : Prop where
  mem_or_neg_mem' (x : R) : x ∈ P ∨ -x ∈ P
  mem_or_mem' {x y : R} (h : x * y ∈ AddSubgroup.support P) :
    x ∈ AddSubgroup.support P ∨ y ∈ AddSubgroup.support P

instance isOrdering [IsPrimeOrdering P] :
    IsOrdering P where
  mem_or_neg_mem' := IsPrimeOrdering.mem_or_neg_mem'

end RingPreordering
