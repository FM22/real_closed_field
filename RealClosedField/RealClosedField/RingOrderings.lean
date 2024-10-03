/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.Order.Zorn

/-
## Definitions
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
lemma RingPreorderingClass.toRingPreordering_coe (P : S) : (toRingPreordering P : Set R) = P := by
  rw [toRingPreordering]; aesop

end defns

/- Construct a preordering from a minimal set of axioms. -/
def RingPreordering.mk' {R : Type*} [CommRing R] (P : Set R)
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

@[aesop safe apply (rule_sets := [SetLike])]
theorem RingPreordering.inv_mem
    {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] {P : S} {a : F}
    (ha : a ∈ P) : a⁻¹ ∈ P := by
  rw [(by field_simp : a⁻¹ = a * (a⁻¹ * a⁻¹))]
  aesop

theorem RingPreodering.nonempty_chain_bddAbove {R : Type*} [CommRing R]
    (c : Set (RingPreordering R)) (hcc : IsChain (· ≤ ·) c) (hc : c.Nonempty) : BddAbove c := by
  rw [bddAbove_def]
  let c' := RingPreordering.toSubsemiring '' c
  have hc'c : IsChain (· ≤ ·) c' := IsChain.image _ _ RingPreordering.toSubsemiring (by aesop) hcc
  let Q := RingPreordering.mk (sSup c')
    (fun x => by
      have : hc.some.toSubsemiring ≤ (sSup c') :=
        CompleteLattice.le_sSup _ _ (by aesop (add hc.some_mem unsafe))
      exact this (by simpa using (hc.some.square_mem' x)))
    (by
      have : ∀ x ∈ c', -1 ∉ x := fun _ hP' => by
        obtain ⟨P, _, rfl⟩ := (Set.mem_image _ _ _).mp hP'
        simpa using P.minus_one_not_mem'
      simpa [Subsemiring.coe_sSup_of_directedOn (by simp [c', hc]) (IsChain.directedOn hc'c)])
  refine ⟨Q, fun P _ => ?_⟩
  have : P.toSubsemiring ≤ Q.toSubsemiring := CompleteLattice.le_sSup c' P.toSubsemiring (by aesop)
  aesop

/-
## Constructing larger orderings
-/

section adjoin_linear

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] (P : S) (a : R)

/-- An explicit form of the semiring generated by `P` and `a`. -/
def RingPreordering.adjoin_linear : Subsemiring R where
  carrier := {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}
  zero_mem' := ⟨0, by aesop, 0, by aesop, by simp⟩
  one_mem' := ⟨1, by aesop, 0, by aesop, by simp⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ha
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hb
    exact ⟨x₁ + x₂, by aesop, y₁ + y₂, by aesop, by ring⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ha
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hb
    exact ⟨x₁ * x₂ + (a * a) * (y₁ * y₂), by aesop, x₁ * y₂ + y₁ * x₂, by aesop, by ring⟩

theorem Subsemiring.closure_insert_ringPreordering :
    Subsemiring.closure (insert a P) = RingPreordering.adjoin_linear P a := by
  apply closure_eq_of_le
  · intro x hx; rcases hx with ⟨_,_⟩ | hP
    · exact ⟨0, by aesop, 1, by aesop, by simp⟩;
    · exact ⟨x, by aesop, 0, by aesop, by simp⟩
  · intro z hz; obtain ⟨x, hx, y, hy, rfl⟩ := hz; aesop

end adjoin_linear

section adjoin_field

variable {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] (P : S)

/- set_option trace.aesop true -/

/--
If `F` is a field, `P` is a preordering on `F`, and `a` is an element of `P` such that `-a ∉ P`,
then `-1` is not of the form `x + a * y` for any `x` and `y` in `P`.
This is the crucial fact that allows preorderings to be extended by unordered elements.
-/
theorem RingPreordering.minus_one_not_mem_adjoin_linear
    (a : F) (ha : -a ∉ P) (x y : F) (hx : x ∈ P) (hy : y ∈ P) :
    -1 ≠ x + a * y := by
  intro hz
  apply ha
  have : y ≠ 0 := fun _ => by simpa [*] using minus_one_not_mem P
  rw [show -a = x * y⁻¹ + y⁻¹ by
    field_simp
    rw [neg_eq_iff_eq_neg.mp hz]
    ring]
  aesop

/-
If `F` is a field, `P` is a preordering on `F`, and `a` in `F` is such that `-a ∉ P`,
then the semiring generated by `P` and `a` is still a preordering on `F`.
-/
def RingPreordering.adjoin {a : F} (ha : -a ∉ P) : RingPreordering F where
  __ := Subsemiring.closure (insert a P)
  square_mem' {x} := by
    simpa using Subsemiring.closure_mono
      (by simp : ↑P ⊆ insert a ↑P)
      (Subsemiring.subset_closure <| square_mem P _)
  minus_one_not_mem' := by
    have : ¬ ∃ x ∈ P, ∃ y ∈ P, -1 = x + a * y :=
      by aesop (add (minus_one_not_mem_adjoin_linear P a ha) norm)
    have : -1 ∉ adjoin_linear P a := this
    simpa [Subsemiring.closure_insert_ringPreordering] using this

lemma RingPreordering.subset_adjoin {a : F} (ha : -a ∉ P) : (P : Set F) ⊆ adjoin P ha := by
  simpa using Subsemiring.closure_mono (by simp : ↑P ⊆ insert a ↑P)

lemma RingPreordering.mem_adjoin {a : F} (ha : -a ∉ P) : a ∈ adjoin P ha := by
  simpa using Subsemiring.subset_closure (by simp : a ∈ insert a ↑P)

def RingPreordering.toOrdering (P : RingPreordering F) (h : IsMax P) : RingOrdering F where
  __ := P
  mem_or_neg_mem' {x} := by
    by_contra
    have hx : x ∉ P ∧ -x ∉ P := by aesop
    have : (P : Set F) ⊂ adjoin P hx.2 := by
      rw [Set.ssubset_iff_of_subset (subset_adjoin P hx.2)]
      exact ⟨x, mem_adjoin P hx.2, hx.1⟩
    exact not_isMax_of_lt (by aesop) h

theorem RingPreordering.exists_le_ordering : ∃ O : RingOrdering F, (P : Set F) ⊆ O := by
  suffices ∃ Q, RingPreorderingClass.toRingPreordering P ≤ Q ∧ Maximal (fun x ↦ x ∈ Set.univ) Q by
    obtain ⟨Q, hQl, hQm⟩ := this
    refine ⟨Q.toOrdering (by aesop), by aesop⟩
  apply zorn_le_nonempty₀
  · intro c _ hc P' hP'
    simp_all [← bddAbove_def, RingPreodering.nonempty_chain_bddAbove c hc (Set.nonempty_of_mem hP')]
  · simp

end adjoin_field

/- maybe have the below in a new file? or in the formally real file? need to think about dependencies -/

/- semireal ring : sums of squares form a RingPreordering -/

/- formally real field : RingOrdering exists -/

/- link RingOrdering to RingCone etc. -/
