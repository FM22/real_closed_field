/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Order
import RealClosedField.RealClosedField.RingOrdering.Basic

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide the structure `RingCone`
that encodes axioms of `OrderedRing` and `LinearOrderedRing`
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

namespace RingCone

variable {T : Type*} [OrderedRing T] {a : T}

variable (T) in
/-- Construct a cone from the set of non-negative elements of a partially ordered ring. -/
def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

@[simp] lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl
@[simp] lemma nonneg_toAddGroupCone : (nonneg T).toAddGroupCone = .nonneg T := rfl
@[simp] lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl
@[simp, norm_cast] lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl

instance nonneg.isMaxCone {T : Type*} [LinearOrderedRing T] : IsMaxCone (nonneg T) where
  mem_or_neg_mem := mem_or_neg_mem (C := AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] [RingConeClass S R] (C : S)

/-- Construct a partially ordered ring by designating a cone in a ring.
Warning: using this def as a constructor in an instance can lead to diamonds
due to non-customisable field: `lt`. -/
@[reducible] def OrderedRing.mkOfCone : OrderedRing R where
  __ := ‹Ring R›
  __ := OrderedAddCommGroup.mkOfCone C
  zero_le_one := show _ ∈ C by simpa using one_mem C
  mul_nonneg x y xnn ynn := show _ ∈ C by simpa using mul_mem xnn ynn

/-- Construct a linearly ordered domain by designating a maximal cone in a domain.
Warning: using this def as a constructor in an instance can lead to diamonds
due to non-customisable fields: `lt`, `decidableLT`, `decidableEq`, `compare`. -/
@[reducible] def LinearOrderedRing.mkOfCone
    [IsDomain R] [IsMaxCone C]
    (dec : DecidablePred (· ∈ C)) : LinearOrderedRing R where
  __ := OrderedRing.mkOfCone C
  __ := OrderedRing.toStrictOrderedRing R
  le_total a b := by simpa using mem_or_neg_mem (b - a)
  decidableLE a b := dec _

instance RingConeClass.instSetLike_of_isMaxCone {S R : Type*}
    [CommRing R] [SetLike S R] [RingConeClass S R] : SetLike {x : S // IsMaxCone x} R
    where
  coe x := ↑x.val
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance RingConeClass.instRingConeClass_of_isMaxCone {S R : Type*}
    [CommRing R] [SetLike S R] [RingConeClass S R] : RingConeClass {x : S // IsMaxCone x} R where
  add_mem := add_mem (S := S)
  zero_mem {s} := zero_mem (s : S)
  mul_mem := mul_mem (S := S)
  one_mem {s} := one_mem (s : S)
  eq_zero_of_mem_of_neg_mem := eq_zero_of_mem_of_neg_mem (S := S)

open Classical in
/-- A maximal cone over a commutative ring `R` is an ordering on `R`. -/
instance RingConeClass.instRingOrderingClass_of_isMaxCone {S R : Type*} [Nontrivial R]
    [CommRing R] [SetLike S R] [RingConeClass S R] :
    RingOrderingClass {x : S // IsMaxCone x} (R := R) where
  __ := RingConeClass.toSubsemiringClass
  square_mem P x := by
    cases @mem_or_neg_mem S _ _ _ _ P.2 x with
    | inl hx  => aesop
    | inr hnx => have : -x * -x ∈ P := by aesop (config := { enableSimp := false })
                 simpa
  minus_one_not_mem P h := one_ne_zero <| eq_zero_of_mem_of_neg_mem (one_mem ↑P) h
  mem_or_neg_mem P x := @mem_or_neg_mem S _ _ _ _ P.2 x

/- TODO : decide whether to keep this cursed subtype instance, or whether to change to a def. -/
