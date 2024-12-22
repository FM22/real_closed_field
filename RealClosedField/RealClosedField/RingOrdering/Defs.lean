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

variable (R : Type*) [CommRing R]

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
@[ext]
structure RingPreordering extends Subsemiring R where
  square_mem' (x : R) : x * x ∈ carrier
  minus_one_not_mem' : -1 ∉ carrier

namespace RingPreordering

attribute [coe] toSubsemiring

instance : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance : SubsemiringClass (RingPreordering R) R where
  zero_mem _ := Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

variable {R}

@[aesop safe 0 apply (rule_sets := [SetLike])]
protected theorem square_mem (P : RingPreordering R) (x : R) : x * x ∈ P :=
  RingPreordering.square_mem' _ _

@[aesop unsafe 20% forward (rule_sets := [SetLike])]
protected theorem minus_one_not_mem (P : RingPreordering R) : -1 ∉ P :=
  RingPreordering.minus_one_not_mem' _

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R → _) := fun A B h => by ext; rw [h]

@[simp]
theorem toSubsemiring_eq {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := toSubsemiring_injective.eq_iff

@[simp]
theorem mem_toSubsemiring {P : RingPreordering R} {x : R} :
  x ∈ P.toSubsemiring ↔ x ∈ P := Iff.rfl

@[simp]
theorem coe_toSubsemiring {P : RingPreordering R} :
  (P.toSubsemiring : Set R) = P := rfl

section copy

variable (P : RingPreordering R) (S : Set R) (hS : S = P)

/-- Copy of a preordering with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy : RingPreordering R where
  carrier := S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop
  square_mem' := by aesop
  minus_one_not_mem' := by aesop

@[simp]
theorem coe_copy : (P.copy S hS : Set R) = S := rfl

theorem copy_eq : P.copy S hS = S := rfl

end copy

variable {P : RingPreordering R}

/-!
## Support
-/

namespace AddSubgroup

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

@[simp]
lemma support_toAddSubgroup : (support P).toAddSubgroup = AddSubgroup.support P := by ext; simp

end Ideal

/-!
## (Prime) orderings
-/

variable (P) in
/-- An ordering `P` on a ring `R` is a preordering such that, for every `x` in `R`,
either `x` or `-x` lies in `P`. -/
class IsOrdering : Prop where
  mem_or_neg_mem' (x : R) : x ∈ P ∨ -x ∈ P

variable (P) in
/-- Technical lemma to get P as explicit argument -/
protected lemma mem_or_neg_mem [IsOrdering P] :
    ∀ x : R, x ∈ P ∨ -x ∈ P := IsOrdering.mem_or_neg_mem' (P := P)

variable (P) in
/-- A prime ordering `P` on a ring `R` is an ordering whose support is a prime ideal. -/
class IsPrimeOrdering : Prop where
  mem_or_neg_mem' (x : R) : x ∈ P ∨ -x ∈ P
  mem_or_mem' {x y : R} (h : x * y ∈ AddSubgroup.support P) :
    x ∈ AddSubgroup.support P ∨ y ∈ AddSubgroup.support P

instance IsPrimeOrdering.instIsOrdering [IsPrimeOrdering P] :
    IsOrdering P where
  mem_or_neg_mem' := IsPrimeOrdering.mem_or_neg_mem'

end RingPreordering
