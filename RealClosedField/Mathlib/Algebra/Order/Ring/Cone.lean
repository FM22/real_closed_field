/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import RealClosedField.Mathlib.Algebra.Order.Group.Cone
import RealClosedField.Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide structures `RingCone` and `MaximalRingCone`
that encode axioms of `OrderedRing` and `LinearOrderedRing`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in rings and the corresponding ordered rings.
-/

/-- `RingConeClass S R` says that `S` is a type of cones in `R`. -/
class RingConeClass (S R : Type*) [Ring R] [SetLike S R]
    extends AddGroupConeClass S R, SubsemiringClass S R : Prop

/-- A (positive) cone in a ring is a subsemiring that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the ring into a partially ordered ring. -/
structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

/-- Interpret a cone in a ring as a cone in the underlying additive group. -/
add_decl_doc RingCone.toAddGroupCone

instance RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance RingCone.instRingConeClass (R : Type*) [Ring R] :
    RingConeClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

/-- Typeclass for (ring) cones containing all squares. -/
class HasSquaresCone {S R : Type*} [Ring R] [SetLike S R] (C : S) : Prop where
  square_mem (a : R) : a * a ∈ C

instance RingCone.withSquares_of_max {S R : Type*} [Ring R] [IsDomain R] [SetLike S R]
    [RingConeClass S R] (C : S) [IsMaxCone C] : HasSquaresCone C where
  square_mem _ := Or.elim (IsMaxCone.mem_or_neg_mem _)
                          (fun ha => mul_mem ha ha)
                          (fun hna => by simpa using mul_mem hna hna)

namespace RingCone
variable {T : Type*} [OrderedRing T] {a : T}

variable (T) in
/-- Construct a cone from the set of non-negative elements of a partially ordered ring. -/
def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

@[simp] lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl
@[simp] lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl
@[simp, norm_cast] lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl

instance nonneg.isMaxCone {T : Type*} [LinearOrderedRing T] : IsMaxCone (nonneg T) where
  mem_or_neg_mem := IsMaxCone.mem_or_neg_mem (C := AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] [RingConeClass S R] (C : S)

/-- A cone over a nontrivial ring does not conain -1. -/
theorem RingConeClass.neg_one_not_mem [Nontrivial R] : -1 ∉ C :=
  fun h => zero_ne_one' R (eq_zero_of_mem_of_neg_mem (one_mem C) h).symm

/-- Construct a partially ordered ring by designating a positive cone in a ring. -/
@[reducible] def OrderedRing.mkOfCone : OrderedRing R where
  __ := ‹Ring R›
  __ := OrderedAddCommGroup.mkOfCone C
  zero_le_one := show _ ∈ C by simpa using one_mem C
  mul_nonneg x y xnn ynn := show _ ∈ C by simpa using mul_mem xnn ynn

/-- Construct a linearly ordered domain by designating a positive cone in a domain. -/
@[reducible] def LinearOrderedRing.mkOfCone [IsDomain R] [IsMaxCone C]
    (dec : DecidablePred (· ∈ C)) : LinearOrderedRing R where
  __ := OrderedRing.mkOfCone C
  __ := OrderedRing.toStrictOrderedRing R
  le_total a b := by simpa using IsMaxCone.mem_or_neg_mem (b - a)
  decidableLE a b := dec _
