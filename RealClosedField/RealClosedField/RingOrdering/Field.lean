/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.RealClosedField.RingOrdering.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Zorn

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

variable {P} in
@[aesop safe apply (rule_sets := [SetLike])]
theorem RingPreordering.inv_mem' {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  rw [(by field_simp : a⁻¹ = a * (a⁻¹ * a⁻¹))]
  aesop

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

/- If `F` is a field and `P` is a preordering on `F` that is maximal with respect to inclusion,
then `P` is an ordering.-/
def RingPreordering.toOrdering (P : RingPreordering F) (h : IsMax P) : RingOrdering F where
  __ := P
  mem_or_neg_mem' {x} := by
    by_contra
    have hx : x ∉ P ∧ -x ∉ P := by aesop
    have : (P : Set F) ⊂ adjoin P hx.2 := by
      rw [Set.ssubset_iff_of_subset (subset_adjoin P hx.2)]
      exact ⟨x, mem_adjoin P hx.2, hx.1⟩
    exact not_isMax_of_lt (by aesop) h

/- If `F` is a field, then every preordering on `F` extends to an ordering. -/
theorem RingPreordering.exists_le_ordering : ∃ O : RingOrdering F, (P : Set F) ⊆ O := by
  suffices ∃ Q, RingPreorderingClass.toRingPreordering P ≤ Q ∧ Maximal (fun x ↦ x ∈ Set.univ) Q by
    obtain ⟨Q, _⟩ := this
    exact ⟨Q.toOrdering (by aesop), by aesop⟩
  apply zorn_le_nonempty₀
  · intro c _ hc P' hP'
    simp_all [← bddAbove_def,
              RingPreordering.nonempty_chain_bddAbove c hc (Set.nonempty_of_mem hP')]
  · simp

end adjoin_field
