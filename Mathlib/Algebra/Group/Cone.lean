/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide structures `GroupCone` and `MaximalGroupCone`
that encode axioms of `OrderedCommGroup` and `LinearOrderedCommGroup`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

/-- `AddGroupConeClass S G` says that `S` is a type of cones in `G`. -/
class AddGroupConeClass (S G : Type*) [AddCommGroup G] [SetLike S G] extends
    AddSubmonoidClass S G : Prop where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive]
class GroupConeClass (S G : Type*) [CommGroup G] [SetLike S G] extends
    SubmonoidClass S G : Prop where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1

export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group. -/
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group. -/
@[to_additive]
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier → a = 1

@[to_additive]
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

/-- `MaximalAddGroupConeClass S G` says that `S` is a type of maximal cones in `G`. -/
class MaximalAddGroupConeClass (S G : Type*) [AddCommGroup G] [SetLike S G]
    extends AddGroupConeClass S G : Prop where
  mem_or_neg_mem (C : S) (a : G) : a ∈ C ∨ -a ∈ C

/-- `MaximalGroupConeClass S G` says that `S` is a type of maximal cones in `G`. -/
@[to_additive]
class MaximalGroupConeClass (S G : Type*) [CommGroup G] [SetLike S G]
    extends GroupConeClass S G : Prop where
  mem_or_inv_mem (C : S) (a : G) : a ∈ C ∨ a⁻¹ ∈ C

export MaximalGroupConeClass (mem_or_inv_mem)
export MaximalAddGroupConeClass (mem_or_neg_mem)

/-- A maximal (positive) cone in an abelian group is a cone containing
either `a` or `-a` for every `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a linearly ordered group. -/
structure MaximalAddGroupCone (G : Type*) [AddCommGroup G]
    extends AddGroupCone G where
  mem_or_neg_mem' a : a ∈ carrier ∨ -a ∈ carrier

/-- A maximal (positive) cone in an abelian group is a cone containing
either `a` or `a⁻¹` for every `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a linearly ordered group. -/
@[to_additive]
structure MaximalGroupCone (G : Type*) [CommGroup G] extends GroupCone G where
  mem_or_inv_mem' a : a ∈ carrier ∨ a⁻¹ ∈ carrier

@[to_additive]
instance MaximalGroupCone.instSetLike (G : Type*) [CommGroup G] :
  SetLike (MaximalGroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]
instance MaximalGroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (MaximalGroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

@[to_additive]
instance MaximalGroupCone.instMaximalGroupConeClass (G : Type*) [CommGroup G] :
    MaximalGroupConeClass (MaximalGroupCone G) G where
  mem_or_inv_mem {C} := C.mem_or_inv_mem'

namespace GroupCone
variable {H : Type*} [OrderedCommGroup H] {a : H}

variable (H) in
/-- Construct a cone from the set of elements of
a partially ordered abelian group that are at least 1. -/
@[to_additive nonneg
"Construct a cone from the set of non-negative elements of a partially ordered abelian group."]
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp) nonneg_toAddSubmonoid]
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp) mem_nonneg]
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
@[to_additive (attr := simp, norm_cast) coe_nonneg]
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl

end GroupCone

namespace MaximalGroupCone
variable {H : Type*} [LinearOrderedCommGroup H] {a : H}

variable (H) in
/-- Construct a maximal cone from the set of elements of
a linearly ordered abelian group that are at least 1. -/
@[to_additive nonneg
"Construct a maximal cone from the set of non-negative elements of
a linearly ordered abelian group."]
def oneLE : MaximalGroupCone H where
  __ := GroupCone.oneLE H
  mem_or_inv_mem' := by simpa using le_total 1

@[to_additive (attr := simp) nonneg_toAddSubmonoid]
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp) mem_nonneg]
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
@[to_additive (attr := simp, norm_cast) coe_nonneg]
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl

end MaximalGroupCone

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive (attr := reducible)
"Construct a partially ordered abelian group by designating a cone in an abelian group."]
def OrderedCommGroup.mkOfCone [GroupConeClass S G] :
    OrderedCommGroup G where
  le a b := b / a ∈ C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)
  mul_le_mul_left a b nab c := by simpa using nab

/-- Construct a linearly ordered abelian group by designating a maximal cone in an abelian group. -/
@[to_additive (attr := reducible)
"Construct a linearly ordered abelian group by designating a maximal cone in an abelian group."]
def LinearOrderedCommGroup.mkOfCone
    [MaximalGroupConeClass S G] (dec : DecidablePred (· ∈ C)) :
    LinearOrderedCommGroup G where
  __ := OrderedCommGroup.mkOfCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  decidableLE a b := dec _