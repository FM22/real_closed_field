/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.RealClosedField.RingOrdering.Basic

import Mathlib.Order.Zorn

/-
## Adjoining an element to a preordering
-/

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] (P : S) (a : R)

namespace Subsemiring

/-- An explicit form of the semiring generated by a preordering `P` and an element `a`. -/
def ringPreordering_adjoin : Subsemiring R where
  carrier := {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}
  zero_mem' := ⟨0, by aesop, 0, by aesop, by simp⟩
  one_mem' := ⟨1, by aesop, 0, by aesop, by simp⟩
  add_mem' := fun ha hb => by
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ha
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hb
    exact ⟨x₁ + x₂, by aesop, y₁ + y₂, by aesop, by ring⟩
  mul_mem' := fun ha hb => by
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ha
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hb
    exact ⟨x₁ * x₂ + (a * a) * (y₁ * y₂), by aesop, x₁ * y₂ + y₁ * x₂, by aesop, by ring⟩

variable {P} in
@[aesop unsafe 70% apply (rule_sets := [SetLike])]
lemma subset_ringPreordering_adjoin {x : R} (hx : x ∈ P) :
    x ∈ ringPreordering_adjoin P a := ⟨x, by aesop, 0, by aesop, by simp⟩

@[aesop safe 0 apply (rule_sets := [SetLike])]
lemma mem_ringPreordering_adjoin : a ∈ ringPreordering_adjoin P a :=
  ⟨0, by aesop, 1, by aesop, by simp⟩

@[aesop safe 0 apply (rule_sets := [SetLike])]
lemma square_mem_ringPreordering_adjoin (x : R) : x * x ∈ ringPreordering_adjoin P a :=
  by simpa using subset_ringPreordering_adjoin a (by aesop)

theorem closure_insert_eq_ringPreordering_adjoin :
    closure (insert a P) = ringPreordering_adjoin P a :=
  closure_eq_of_le (fun _ => by aesop) (fun _ ⟨_, _, _, _, _⟩ => by aesop)

end Subsemiring

namespace RingPreordering

variable {P a} in
def adjoin (h : -1 ∉ Subsemiring.ringPreordering_adjoin P a) :
    RingPreordering R where
  __ := Subsemiring.ringPreordering_adjoin P a
  square_mem' := by aesop
  minus_one_not_mem' := h

variable {P a} in
@[aesop unsafe 70% apply (rule_sets := [SetLike])]
lemma subset_adjoin' (h : -1 ∉ Subsemiring.ringPreordering_adjoin P a) {x : R} (hx : x ∈ P) :
    x ∈ adjoin h := Subsemiring.subset_ringPreordering_adjoin a hx

variable {P a} in
lemma subset_adjoin (h : -1 ∉ Subsemiring.ringPreordering_adjoin P a) : (P : Set R) ⊆ adjoin h :=
  fun _ => by aesop

variable {P a} in
@[aesop safe 0 apply (rule_sets := [SetLike])]
lemma mem_adjoin (h : -1 ∉ Subsemiring.ringPreordering_adjoin P a) : a ∈ adjoin h :=
  Subsemiring.mem_ringPreordering_adjoin P a

/-
## Sufficient conditions for adjoining an element
-/

variable {P} in
theorem minus_one_not_mem_or {x y : R} (h : - (x * y) ∈ P) :
    -1 ∉ Subsemiring.ringPreordering_adjoin P x ∨ -1 ∉ Subsemiring.ringPreordering_adjoin P y := by
  by_contra
  apply minus_one_not_mem P
  have ⟨s₁, hs₁, s₂, hs₂, eqx⟩ : -1 ∈ Subsemiring.ringPreordering_adjoin P x := by aesop
  have ⟨t₁, ht₁, t₂, ht₂, eqy⟩ : -1 ∈ Subsemiring.ringPreordering_adjoin P y := by aesop
  rw [show -1 = (-(x * y)) * s₂ * t₂ + s₁ + t₁ + (s₁ * t₁) by
    linear_combination (t₁ + 1) * eqx - 1 * x * s₂ * eqy]
  aesop (config := { enableSimp := false })

theorem minus_one_not_mem_or' :
    -1 ∉ Subsemiring.ringPreordering_adjoin P a ∨ -1 ∉ Subsemiring.ringPreordering_adjoin P (-a) :=
  RingPreordering.minus_one_not_mem_or (by aesop : - (a * (-a)) ∈ P)

theorem minus_one_not_mem_ringPreordering_adjoin
    (h : ∀ x y, x ∈ P → y ∈ P → x + (1 + y) * a + 1 ≠ 0) :
    -1 ∉ Subsemiring.ringPreordering_adjoin P a := fun contr => by
  have ⟨x, hx, y, hy, eqn⟩ : -1 * (1 + a) ∈ Subsemiring.ringPreordering_adjoin P a :=
    by aesop (config := { enableSimp := false })
  exact h _ _ hx hy (show x + (1 + y) * a + 1 = 0 by linear_combination -(1 * eqn))

/--
If `F` is a field, `P` is a preordering on `F`, and `a` is an element of `P` such that `-a ∉ P`,
then `-1` is not of the form `x + a * y` with `x` and `y` in `P`.
-/
theorem minus_one_not_mem_adjoin_linear
    {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] {P : S} {a : F}
    (ha : -a ∉ P) : -1 ∉ Subsemiring.ringPreordering_adjoin P a := fun ⟨x, hx, y, hy, eqn⟩ =>
  ha <| by
  have : y ≠ 0 := fun _ => by simpa [*] using minus_one_not_mem P
  rw [show -a = x * y⁻¹ + y⁻¹ by field_simp; linear_combination eqn]
  aesop

/-
## Existence of prime orderings
-/

theorem exists_le :
    ∃ Q : RingPreordering R, (P : Set R) ⊆ Q ∧ (a ∈ Q ∨ -a ∈ Q) := by
  cases RingPreordering.minus_one_not_mem_or' P a with
  | inl h => exact ⟨adjoin h, subset_adjoin _, by aesop⟩
  | inr h => exact ⟨adjoin h, subset_adjoin _, by aesop⟩

theorem exists_lt (hp : a ∉ P) (hn : -a ∉ P) :
    ∃ Q : RingPreordering R, (P : Set R) ⊂ Q := by
  rcases exists_le P a with ⟨Q, le, p_mem | n_mem⟩
  · exact ⟨Q, lt_of_le_of_ne le <| Ne.symm (ne_of_mem_of_not_mem' p_mem hp)⟩
  · exact ⟨Q, lt_of_le_of_ne le <| Ne.symm (ne_of_mem_of_not_mem' n_mem hn)⟩

/- A preordering on `R` that is maximal with respect to inclusion is a prime ordering. -/
theorem isPrimeOrdering_of_maximal {O : RingPreordering R} (max : IsMax O) :
    IsPrimeOrdering O := isPrimeOrdering_iff.mpr (fun a b h => by
  cases RingPreordering.minus_one_not_mem_or h with
  | inl h => exact Or.inl <| max (subset_adjoin h) (mem_adjoin h)
  | inr h => exact Or.inr <| max (subset_adjoin h) (mem_adjoin h))

/- Every preordering on `R` extends to a prime ordering. -/
theorem exists_le_isPrimeOrdering :
    ∃ O : RingPreordering R, (P : Set R) ⊆ O ∧ IsPrimeOrdering O := by
  have ⟨O, le, hO⟩ : ∃ O, RingPreorderingClass.toRingPreordering P ≤ O ∧ IsMax O := by
    refine zorn_le_nonempty_Ici₀ _ (fun _ _ hc _ hQ => ?_) _ (by trivial)
    simp_all [← bddAbove_def, nonempty_chain_bddAbove _ hc (Set.nonempty_of_mem hQ)]
  exact ⟨O, by aesop, isPrimeOrdering_of_maximal hO⟩

/- A prime ordering on `R` is maximal among preorderings iff it is maximal among prime orderings. -/
theorem maximal_isPrimeOrdering_iff_maximal {O : RingPreordering R} [IsPrimeOrdering O] :
    IsMax O ↔ Maximal IsPrimeOrdering O := by
  refine Iff.intro (fun h => ?_) (fun hO P le₁ => ?_)
  · exact Maximal.mono (by simpa using h) (fun _ _ => trivial) (inferInstance)
  · rcases exists_le_isPrimeOrdering P with ⟨Q, le₂, hQ⟩
    aesop (add safe forward le_trans, safe forward Maximal.eq_of_ge)
