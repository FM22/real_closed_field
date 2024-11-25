/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Order.Chain
import Mathlib.Tactic.Ring
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Ideal.Basic

/-
## Definitions
-/

section Defns

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

/-- `RingOrderingClass S R` says that `S` is a type of orderings on `R`. -/
class RingOrderingClass extends RingPreorderingClass S R : Prop where
  mem_or_neg_mem (P : S) (x : R) : x ∈ P ∨ -x ∈ P

export RingOrderingClass (mem_or_neg_mem)

/-- An ordering `P` on a ring `R` is a preordering such that, for every `x` in `R`,
either `x` or `-x` lies in `P`. Equivalently, an ordering is a maximal preordering. -/
structure RingOrdering extends RingPreordering R where
  mem_or_neg_mem' (x : R) : x ∈ carrier ∨ -x ∈ carrier

instance RingOrdering.instSetLike : SetLike (RingOrdering R) R where
  coe P := P.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance RingOrdering.instRingOrderingClass : RingOrderingClass (RingOrdering R) R where
  zero_mem {P} := P.zero_mem'
  one_mem {P} := P.one_mem'
  add_mem {P} := P.add_mem'
  mul_mem {P} := P.mul_mem'
  square_mem {P} := P.square_mem'
  minus_one_not_mem {P} := P.minus_one_not_mem'
  mem_or_neg_mem {P} := P.mem_or_neg_mem'

variable{S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R]

def RingPreorderingClass.toRingPreordering (P : S) :
    RingPreordering R where
  carrier := P
  zero_mem' := zero_mem P
  one_mem' := one_mem P
  add_mem' := add_mem
  mul_mem' := mul_mem
  square_mem' := square_mem P
  minus_one_not_mem' := minus_one_not_mem P

@[simp]
lemma RingPreorderingClass.coe_toRingPreordering (P : S) : (toRingPreordering P : Set R) = P := by
  rw [toRingPreordering]; aesop

end Defns

namespace RingPreordering

/-
## Basic properties
-/

@[aesop safe apply (rule_sets := [SetLike])]
theorem inv_mem
    {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] {P : S} {a : Rˣ}
    (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  rw [(by simp : (↑a⁻¹ : R) = a * (a⁻¹ * a⁻¹))]
  aesop (config := { enableSimp := false })

/- Construct a preordering from a minimal set of axioms. -/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add   : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul   : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq    : ∀ x : R, x * x ∈ P)
    (minus : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  square_mem' x := by simpa using sq x
  minus_one_not_mem' := by simpa using minus
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

theorem nonempty_chain_bddAbove {R : Type*} [CommRing R]
    (c : Set (RingPreordering R)) (hcc : IsChain (· ≤ ·) c) (hc : c.Nonempty) : BddAbove c := by
  rw [bddAbove_def]
  let Q := mk (sSup (toSubsemiring '' c))
    (fun x => CompleteLattice.le_sSup _ hc.some.toSubsemiring (by aesop (add hc.some_mem safe))
              (by simpa using (hc.some.square_mem' x)))
    (by
      have a : ∀ x ∈ (toSubsemiring '' c), -1 ∉ x := fun P' hP' => by
        obtain ⟨P, _, rfl⟩ := (by aesop : ∃ x ∈ c, x.toSubsemiring = P')
        simpa using P.minus_one_not_mem'
      aesop (add (Subsemiring.coe_sSup_of_directedOn (by simp [hc])
        (IsChain.directedOn (IsChain.image _ _ _ (by aesop) hcc))) norm))
  refine ⟨Q, fun P _ => ?_⟩
  have : P.toSubsemiring ≤ Q.toSubsemiring :=
    CompleteLattice.le_sSup (toSubsemiring '' c) _ (by aesop)
  aesop

end RingPreordering

/-
## Support
-/

variable {S R : Type*} [CommRing R] [SetLike S R] {P : S}

namespace AddSubgroup

variable [RingPreorderingClass S R]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def preordering_support : AddSubgroup R where
  carrier := {x : R | x ∈ P ∧ -x ∈ P}
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

@[simp] lemma mem_support : x ∈ preordering_support P ↔ x ∈ P ∧ -x ∈ P := Iff.rfl
@[simp, norm_cast] lemma coe_support : preordering_support P = {x : R | x ∈ P ∧ -x ∈ P} := rfl

end AddSubgroup

variable (P) in
class RingPreorderingClass.HasIdealSupport : Prop where
  smul_mem (x a : R) (ha : a ∈ P) : x * a ∈ P

export RingPreorderingClass.HasIdealSupport (smul_mem)
attribute [aesop safe apply 0 (rule_sets := [SetLike])] smul_mem

namespace Ideal

variable [RingPreorderingClass S R] [RingPreorderingClass.HasIdealSupport P]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def preordering_support : Ideal R where
  carrier := {x : R | x ∈ P ∧ -x ∈ P}
  zero_mem' := by aesop
  add_mem' := by aesop
  smul_mem' := by
    intro c x hx
    have : c * (-x) ∈ P := RingPreorderingClass.HasIdealSupport.smul_mem _ _ (by simp_all)
    aesop

@[simp] lemma mem_support : x ∈ preordering_support P ↔ x ∈ P ∧ -x ∈ P := Iff.rfl
@[simp, norm_cast] lemma coe_support : preordering_support P = {x : R | x ∈ P ∧ -x ∈ P} := rfl

end Ideal

instance RingPreorderingClass.hasIdealSupport [RingOrderingClass S R] :
    RingPreorderingClass.HasIdealSupport P where
  smul_mem x a ha := by sorry

instance RingPreorderingClass.hasIdealSupport' [RingPreorderingClass S R] [Fact (¬ CharP R 2)] :
    RingPreorderingClass.HasIdealSupport P where
  smul_mem x a ha := by sorry
