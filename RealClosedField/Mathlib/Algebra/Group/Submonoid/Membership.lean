/-
Add this lemma to <filepath> alongside new imports
-/

import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators

open Submonoid /-- context -/

@[to_additive]
theorem exists_finset_prod_of_mem_closure {M : Type*} [CommMonoid M] {s : Set M} {x : M}
    (hx : x ∈ closure s) :
    ∃ (α : Type) (I : Finset α) (f : α → M), (∀ i ∈ I, f i ∈ s) ∧ ∏ i ∈ I, f i = x := by
  induction hx using Submonoid.closure_induction_left
  case one                      => exact ⟨Empty, ∅, Empty.elim, by simp⟩
  case mul_left y hy p _ h_prod =>
    rcases h_prod with ⟨α, I, f, hf, ih⟩;
    exact ⟨_, Finset.univ, (Option.elim · y (Subtype.restrict (· ∈ I) f)),
          ⟨by intro i; induction i with
          | none   => simp [hy]
          | some i => simp [Subtype.restrict_apply, hf i],
          by simp [Subtype.restrict_apply, Finset.prod_attach, ih]⟩⟩
