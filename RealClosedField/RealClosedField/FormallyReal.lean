import RealClosedField.Mathlib.Algebra.Order.Ring.Cone
import RealClosedField.Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic

class IsFormallyReal (R : Type*) [AddCommMonoid R] [Mul R] : Prop where
  eq_zero_of_multiset_sum_of_squares_eq_zero {m : Multiset R} : (m.map fun x => x * x).sum = 0 → m ⊆ {0}

theorem eq_zero_of_sum_of_squares_eq_zero {R : Type*} [AddCommMonoid R] [Mul R] [IsFormallyReal R]
    {ι : Type*} {I : Finset ι} {x : ι → R} {i : ι}
    (hx : ∑ i ∈ I, x i * x i = 0) (hi : i ∈ I) : x i = 0 :=
  by simpa using IsFormallyReal.eq_zero_of_multiset_sum_of_squares_eq_zero (m := I.val.map x) (by simpa) (by simpa using ⟨i, by simpa⟩)

open Classical in
theorem IsFormallyReal.of_eq_zero_of_sum_of_squares_eq_zero (R : Type*) [AddCommMonoid R] [Mul R]
    (h : ∀ {ι : Type} {I : Finset ι} {x : ι → R} {i : ι} (hx : ∑ i ∈ I, x i * x i = 0) (hi : i ∈ I), x i = 0) : IsFormallyReal R where
  eq_zero_of_multiset_sum_of_squares_eq_zero {m} := by
    intro hm v hv
    have := h (ι := ℕ) (I := Finset.range (Multiset.card m)) (x := (m.toList.getD · 0)) (i := List.findIdx (· = v) m.toList)
    sorry
  /- TODO : maybe change definition to use lists instead of multisets to avoid "choice" issue? -/
  /- TODO : maybe write inductive construction of indexing function from finset for arbitrary multiset? -/

theorem isFormallyReal_iff_eq_zero_of_sum_of_squares_eq_zero {R : Type*} [AddCommMonoid R] [Mul R] :
  IsFormallyReal R ↔
    (∀ {ι : Type} {I : Finset ι} {x : ι → R} {i : ι} (hx : ∑ i ∈ I, x i * x i = 0) (hi : i ∈ I), x i = 0) :=
  ⟨fun _ => eq_zero_of_sum_of_squares_eq_zero, IsFormallyReal.of_eq_zero_of_sum_of_squares_eq_zero _⟩

theorem eq_zero_of_square_eq_zero {R : Type*} [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} {h : a * a = 0} : a = 0 := by
  exact eq_zero_of_sum_of_squares_eq_zero (by simpa : ∑ i : Option Empty, a * a = 0) (i := default) (by simp)

theorem eq_zero_of_isSumSq_of_sum_eq_zero {R : Type*} [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {S₁ S₂ : R}
    (hS₁ : IsSumSq S₁) (hS₂ : IsSumSq S₂) (h : S₁ + S₂ = 0) : S₁ = 0 := by
  rw [isSumSq_iff_exists_sum] at *
  obtain ⟨ι, I, x, h1⟩ := hS₁; obtain ⟨β, J, y, h2⟩ := hS₂
  rw [h1] at h ⊢; rw [h2] at h
  suffices ∀ i ∈ I, x i = 0 by simpa using Finset.sum_eq_zero (f := fun i => x i * x i) (fun _ h => by simp [this _ h])
  have : ∑ i ∈ I.disjSum J, Sum.elim x y i * Sum.elim x y i = 0 := by simpa
  exact fun i hi => eq_zero_of_sum_of_squares_eq_zero this (i := Sum.inl i) (by simpa)

open Classical in
theorem IsFormallyReal.of_eq_zero_of_square_and_eq_zero_of_sum (R : Type*) [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0) (hs : ∀ {S₁ S₂ : R}, IsSumSq S₁ → IsSumSq S₂ → S₁ + S₂ = 0 → S₁ = 0) : IsFormallyReal R := by
  rw [isFormallyReal_iff_eq_zero_of_sum_of_squares_eq_zero]
  intros ι I x i hx hi
  have : ∑ j ∈ I \ {i}, x j * x j + x i * x i = 0 := by simpa [hx] using Finset.sum_sdiff (by simpa : {i} ⊆ I) (f := (fun j => x j * x j))
  exact hz (by simpa [hs (S₁ := ∑ j ∈ I \ {i}, x j * x j) (S₂ := x i * x i) (by simp) (by simp) this] using this)

instance [NonAssocSemiring R] [Nontrivial R] [IsFormallyReal R] : IsSemireal R where
  add_one_ne_zero_of_isSumSq a ha := by
    obtain ⟨ι, I, x, rfl⟩ := exists_sum_of_isSumSq ha
    suffices ∑ i : Option I, i.elim 1 (x ·) * i.elim 1 (x ·) ≠ 0 by simpa [Finset.sum_attach _ (fun i => x i * x i)]
    intro h_contr; simpa using eq_zero_of_sum_of_squares_eq_zero h_contr (by simp : none ∈ _)
  /- TODO : try out deducing this from previous two lemmas -/

instance [LinearOrderedRing R] : IsFormallyReal R := by
  rw [isFormallyReal_iff_eq_zero_of_sum_of_squares_eq_zero];
  intros ι I x i hx hi
  sorry
  /- TODO: should be similar to eq_zero_of_isSumSq_of_sum_eq_zero -/

  /- OLD PROOF: -/
  /- mul_self_eq_zero.mp (le_antisymm
    (le_of_eq_of_le (eq_neg_of_add_eq_zero_left is_zero)
                    (Right.neg_nonpos_iff.mpr (IsSumSq.nonneg hS)))
    (mul_self_nonneg a)) -/

namespace RingCone
variable {T : Type*} [CommRing T] [IsFormallyReal T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : RingCone T where
  __ := Subsemiring.sumSqIn T
  eq_zero_of_mem_of_neg_mem' {x} hx hnx :=
    eq_zero_of_isSumSq_of_sum_eq_zero hx hnx (add_neg_cancel x)

@[simp] lemma sumSqIn_toSubsemiring : (sumSqIn T).toSubsemiring = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

instance sumSqIn.hasSquares : HasSquaresCone (sumSqIn T) where
  square_mem _ := by simp

end RingCone
