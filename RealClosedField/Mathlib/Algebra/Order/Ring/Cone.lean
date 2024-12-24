/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import RealClosedField.Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Order
import RealClosedField.RealClosedField.RingOrdering.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide the structure `RingCone`
that encodes axioms of `OrderedRing` and `LinearOrderedRing`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in rings and the corresponding ordered rings.
-/

/-- A (positive) cone in a ring is a subsemiring that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the ring into a partially ordered ring. -/
structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

/-- Interpret a cone in a ring as a cone in the underlying additive group. -/
add_decl_doc RingCone.toAddGroupCone

instance (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance (R : Type*) [Ring R] : SubsemiringClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'

namespace RingCone

protected theorem eq_zero_of_mem_of_neg_mem {R : Type*} [Ring R] {C : RingCone R}
    {a : R} (h₁ : a ∈ C) (h₂ : -a ∈ C) : a = 0 := C.eq_zero_of_mem_of_neg_mem' h₁ h₂

@[simp]
theorem mem_toSubsemiring (R : Type*) [Ring R] (C : RingCone R) {x : R} :
  x ∈ C.toSubsemiring ↔ x ∈ C := Iff.rfl

@[simp]
theorem coe_toSubsemiring (R : Type*) [Ring R] (C : RingCone R) :
    (C.toSubsemiring : Set R) = C := rfl

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
  mem_or_neg_mem' := mem_or_neg_mem <| AddGroupCone.nonneg T

end RingCone

variable {R : Type*} [Ring R] (C : RingCone R)

/-- Construct a partially ordered ring by designating a cone in a ring.
Warning: using this def as a constructor in an instance can lead to diamonds
due to non-customisable field: `lt`. -/
@[reducible] def OrderedRing.mkOfCone : OrderedRing R where
  __ := ‹Ring R›
  __ := OrderedAddCommGroup.mkOfCone C.toAddGroupCone
  zero_le_one := show _ ∈ C by simpa using C.one_mem
  mul_nonneg _ _ hx hy := show _ ∈ C by simpa using C.mul_mem hx hy

/-- Construct a linearly ordered domain by designating a maximal cone in a domain.
Warning: using this def as a constructor in an instance can lead to diamonds
due to non-customisable fields: `lt`, `decidableLT`, `decidableEq`, `compare`. -/
@[reducible] def LinearOrderedRing.mkOfCone
    [IsDomain R] [IsMaxCone C] [DecidablePred (· ∈ C)] : LinearOrderedRing R where
  __ := OrderedRing.mkOfCone C
  __ := OrderedRing.toStrictOrderedRing R
  le_total a b := by simpa using mem_or_neg_mem C (b - a)
  decidableLE a b := _

@[reducible]
def RingPreordering.mkOfCone {R : Type*} [Nontrivial R] [CommRing R] (C : RingCone R) [IsMaxCone C] :
    RingPreordering R where
  __ := RingCone.toSubsemiring C
  isSquare_mem' x := by
    rcases x with ⟨y, rfl⟩
    cases mem_or_neg_mem C y with
    | inl h  => aesop
    | inr h => simpa using (show -y * -y ∈ C by aesop (config := { enableSimp := false }))
  minus_one_not_mem' h := one_ne_zero <| RingCone.eq_zero_of_mem_of_neg_mem (one_mem _) h

/-- A maximal cone over a commutative ring `R` is an ordering on `R`. -/
instance {R : Type*} [CommRing R] [Nontrivial R] (C : RingCone R) [IsMaxCone C] :
    RingPreordering.IsOrdering <| RingPreordering.mkOfCone C where
  mem_or_neg_mem' x := mem_or_neg_mem C x

/- TODO : decide what to do about the maximality typeclasses -/

@[reducible] def RingCone.mkOfRingPreordering {R : Type*} [CommRing R] {P : RingPreordering R}
    (hP : RingPreordering.AddSubgroup.support P = ⊥) : RingCone R where
  __ := P.toSubsemiring
  eq_zero_of_mem_of_neg_mem' {a} := by
    have : ∀ x, x ∈ RingPreordering.AddSubgroup.support P → x ∈ (⊥ : AddSubgroup R) := by simp_all
    rcases hP with -
    aesop
  /- TODO : make this proof less awful -/

instance RingCone.mkOfRingPreordering.inst_isMaxCone {R : Type*} [CommRing R]
    {P : RingPreordering R} [RingPreordering.IsOrdering P]
    (hP : RingPreordering.AddSubgroup.support P = ⊥) : IsMaxCone <| mkOfRingPreordering hP where
  mem_or_neg_mem' := RingPreordering.mem_or_neg_mem P

@[reducible] def LinearOrderedRing.mkOfRingOrdering {R : Type*} [CommRing R] [IsDomain R]
    {P : RingPreordering R} [RingPreordering.IsOrdering P] [DecidablePred (· ∈ P)]
    (hP : RingPreordering.AddSubgroup.support P = ⊥) : LinearOrderedRing R :=
  mkOfCone <| RingCone.mkOfRingPreordering hP

@[reducible] def RingCone.mkOfRingPreordering_field {F : Type*} [Field F] (P : RingPreordering F) :
    RingCone F := mkOfRingPreordering <| RingPreordering.support_eq_bot P

@[reducible] def LinearOrderedRing.mkOfRingPreordering_field {F : Type*} [Field F]
    (P : RingPreordering F) [DecidablePred (· ∈ P)] [RingPreordering.IsOrdering P] :
    LinearOrderedRing F :=
  mkOfCone <| RingCone.mkOfRingPreordering_field P

@[reducible] def RingCone.mkOfRingPreordering_quot {R : Type*} [CommRing R] {P : RingPreordering R}
    [RingPreordering.IsOrdering P] : RingCone (R ⧸ (RingPreordering.Ideal.support P)) :=
  mkOfRingPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) (by aesop)

/- TODO: orderings with support I induce maximal ring cones on R/I -/
/- TODO: ordering on an ID <-> ordering on its fraction field -/
