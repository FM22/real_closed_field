/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Ring.Subsemiring.Order

/-
## Definitions
-/

section defns

variable (S R : Type*) [Ring R] [SetLike S R]

/-- `RingOrderingClass S R` says that `S` is a type of orderings on `R`. -/
class RingOrderingClass extends SubsemiringClass S R : Prop where
  square_mem {P : S} {x : R} : x * x ∈ P
  minus_one_not_mem {P : S} : -1 ∉ P

export RingOrderingClass (square_mem)
export RingOrderingClass (minus_one_not_mem)

/-- An ordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
structure RingOrdering extends Subsemiring R where
  square_mem' {x : R} : x * x ∈ carrier
  minus_one_not_mem' : -1 ∉ carrier

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

end defns

/- Construct an ordering from a minimal set of axioms. -/
def RingOrdering.mk' {R : Type*} [Ring R] (P : Set R)
    (add   : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul   : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq    : ∀ {x : R}, x * x ∈ P)
    (minus : (-1 : R) ∉ P) :
    RingOrdering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  square_mem' {x} := by simpa using sq
  minus_one_not_mem' := by simpa using minus
  zero_mem' := by simpa using @sq 0
  one_mem' := by simpa using @sq 1

/-
## Constructing larger precones
-/

def RingOrdering.adjoin_linear {R : Type*} [CommRing R] (P : RingOrdering R) (a : R) :
    Subsemiring R where
  carrier := {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}
  zero_mem' := by simpa using ⟨0, zero_mem P, 0, zero_mem P, by simp⟩
  one_mem' := by simpa using ⟨1, one_mem P, 0, zero_mem P, by simp⟩
  add_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a b ha hb
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ha
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hb
    exact ⟨x₁ + x₂, add_mem hx₁ hx₂, y₁ + y₂, add_mem hy₁ hy₂, by ring⟩
  mul_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a b ha hb
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ha
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hb
    ring_nf
    exact ⟨x₁ * x₂ + (a * a) * (y₁ * y₂),
          add_mem (mul_mem hx₁ hx₂) (mul_mem square_mem (mul_mem hy₁ hy₂)),
          x₁ * y₂ + y₁ * x₂,
          add_mem (mul_mem hx₁ hy₂) (mul_mem hy₁ hx₂),
          by ring⟩

lemma Subsemiring.closure_insert_ringOrdering
    {R : Type*} [CommRing R] (P : RingOrdering R) (a : R) :
    Subsemiring.closure (insert a P) = RingOrdering.adjoin_linear P a := by
  apply closure_eq_of_le
  · sorry
  · sorry

lemma Subsemiring.mem_closure_insert_ringOrdering
    {R : Type*} [CommRing R] (P : RingOrdering R) (a : R) (x : R) :
    x ∈ Subsemiring.closure (insert a P) ↔ x ∈ RingOrdering.adjoin_linear P a :=
  by rw [← Subsemiring.closure_insert_ringOrdering P a]

/-
In order to prove that `P[a]` is a precone, the remaining property to show is that `-1 ∉ P[a]`. This holds if we work *in a field* and if `-a ∉ P`. The proof goes as follows.

Assume that `-1 ∈ P[a]`. Then `-1 = x + a * y` for some `x, y ∈ P`. If `y = 0`, then `-1 = x ∈ P`, which implies `False` because `P` is precone. So we have proven that `y ≠ 0` and we can write ` -a = x * y * (1 / y) ^ 2 + y * (1 / y) ^ 2`. Since `P` is precone, it contains all the squares in `R`. And since `P` contains `x` and `y` and is stable under addition and multiplication, it contains `-a`. But by assumption `-a ∈ P → False`, so we have proven `False`. Note that the proof is constructive.
-/

lemma minus_one_not_mem_closure_insert_ringOrdering
    {S F : Type*} [Field F] [SetLike S F] [RingOrderingClass S F] (P : S)
    (a : F) (ha : -a ∉ P) :
    ¬ ∃ x ∈ P, ∃ y ∈ P, -1 = x + a * y := by
  intro h
  rcases h with ⟨x, hx, y, hy, hz⟩
  have hy' : y ≠ 0 := by
    intro h
    apply minus_one_not_mem (P := P)
    rw [h, mul_zero, add_zero] at hz
    rw [←hz] at hx
    exact hx
  apply ha
  have aux1 : -a = x * y * (1 / y) ^ 2 + y * (1 / y) ^ 2 := by
    field_simp
    have aux2 : -(a * y) = 1 + x := by
      have aux3 : (-1) * (-1) = (-1) * (x + a * y) := by
        exact congrArg (fun t => (-1) * t) hz
      simp only [mul_neg, mul_one, neg_neg, neg_mul, one_mul, neg_add_rev] at aux3
      rw [aux3]
      ring
    have aux3 : -(a * y) * y = (1 + x) * y := by
      exact congrArg (fun t => t * y) aux2
    ring_nf at aux3
    rw [aux3]
    ring_nf
  rw [aux1]
  apply add_mem
  · apply mul_mem
    · exact mul_mem hx hy
    · rw [pow_two]; exact square_mem (P := P)
  · apply mul_mem
    · exact hy
    · rw [pow_two]; exact square_mem (P := P)

/-
If `F` is a field, `P` is an ordering on `F`, and `a` is an element of `P` such that `-a ∉ P`,
then the semiring-closure of `P` and `a` is still an ordering on `F`.
-/
def RingOrdering.adjoinElem {F : Type*} [Field F] (a : F) (P : RingOrdering F) (ha : -a ∉ P) :
    RingOrdering F where
  __ := Subsemiring.closure (insert a P)
  square_mem' {x} := by
    simpa using Subsemiring.closure_mono (by simp : ↑P ⊆ insert a ↑P)
      (Subsemiring.subset_closure P.square_mem')
  minus_one_not_mem' := by
    simpa [Subsemiring.mem_closure_insert_ringOrdering] using
      minus_one_not_mem_closure_insert_ringOrdering P a ha

/--
Introduce the notation `P[a]` for the set `RingOrdering.adjoinElem a P`.
The underlying set is equal to `{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}`
(see `Subsemiring.closure_ringOrdering_union_singleton`).
-/
notation:max P"["a"]" => RingOrdering.adjoinElem a P


-- #lint
