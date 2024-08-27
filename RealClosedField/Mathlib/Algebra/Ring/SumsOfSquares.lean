/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.BigOperators.Ring
import RealClosedField.Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Sums of squares

We introduce sums of squares in a type `R` endowed with an `[Add R]`, `[Zero R]` and `[Mul R]`
instances. Sums of squares in `R` are defined by an inductive predicate `IsSumSq : R → Prop`:
`0 : R` is a sum of squares and if `S` is a sum of squares, then for all `a : R`, `a * a + S` is a
sum of squares in `R`.

## Declarations

- The predicate `IsSumSq : R → Prop`, defining the property of being a sum of squares in `R`.
- The terms `AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` :
in an additive monoid with multiplication `R` and a semiring `R`, we introduce the terms
`AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` as the submonoid and subsemiring, respectively,
of `R` whose carrier is the subset `{S : R | IsSumSq S}`.

## Theorems

- `IsSquare.isSumSq`, `IsSumSq.mul_self`: a square in `R` is a sum of squares in `R`.
- `IsSumSq.add`: if `S1` and `S2` are sums of squares in `R`, then so is `S1 + S2`.
- `IsSumSq.mul`: if `S1` and `S2` are sums of squares in `R`, then so is `S1 * S2`.
- `IsSumSq.sum` : a finite sum of sums of squares in `R` is a sum of squares.
- `IsSumSq.prod` : a finite product of sums of squares in `R` is a sum of squares.
- `IsSumSq.nonneg`: sums of squares are non-negative.
- `AddSubmonoid.closure_isSquare`: the submonoid of `R` generated by the squares in `R` is the set
of sums of squares in `R`.
- `Subsemiring.closure_isSquare`: the subsemiring of `R` generated by the squares in `R` is the set
of sums of squares in `R`.

-/

variable {R : Type*}

/--
In a type `R` with an addition, a zero element and a multiplication, the property of being a sum of
squares is defined by an inductive predicate: `0 : R` is a sum of squares and if `S` is a sum of
squares, then for all `a : R`, `a * a + S` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add (a S : R) (hS : IsSumSq S) : IsSumSq (a * a + S)

/-- Alternative induction scheme for `IsSumSq` using `IsSquare`. -/
theorem IsSumSq.induction_alt [Mul R] [Add R] [Zero R]
    {p : (S : R) → (h : IsSumSq S) → Prop} (S : R) (hS : IsSumSq S)
    (zero : p 0 zero)
    (sq_add : ∀ x S, (hS : IsSumSq S) → (hx : IsSquare x) → p S hS →
      p (x + S) (by rcases hx with ⟨y, hy⟩; rw [hy]; exact sq_add y S hS)) : p S hS := by
  induction hS with
  | zero => exact zero
  | sq_add a S hS hS_ih => exact sq_add (a * a) S hS (isSquare_mul_self _) hS_ih

/-- In an additive monoid with multiplication,
if `S1` and `S2` are sums of squares, then `S1 + S2` is a sum of squares. -/
theorem IsSumSq.add [AddMonoid R] [Mul R] {S1 S2 : R}
    (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction h1 with
  | zero             => simp [zero_add, h2]
  | sq_add a S pS ih => simpa [add_assoc] using IsSumSq.sq_add a (S + S2) ih

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  rw [← add_zero (a * a)]; exact IsSumSq.sq_add _ _ IsSumSq.zero

/-- In an additive unital magma with multiplication `R`, squares in `R` are sums of squares.
By definition, a square in `R` is a term `x : R` such that `x = y * y` for some `y : R`
and in Mathlib this is known as `IsSquare R` (see Mathlib.Algebra.Group.Even). -/
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSumSq x := by
  rcases hx with ⟨a, ha⟩; simp [ha, IsSumSq.mul_self]

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {a : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, the type `AddSubmonoid.sumSqIn R`
is the submonoid of sums of squares in `R`.
-/
def sumSqIn : AddSubmonoid T where
  carrier := {S : T | IsSumSq S}
  zero_mem' := IsSumSq.zero
  add_mem' := IsSumSq.add

@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end AddSubmonoid

/-- In an additive, commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares. -/
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {α : Type*} {I : Finset α} {f : α → R}
    (hf : ∀ i ∈ I, IsSumSq <| f i) : IsSumSq (∑ i ∈ I, f i) := by
  simpa using AddSubmonoid.sum_mem (AddSubmonoid.sumSqIn R) hf

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine le_antisymm (closure_le.2 (fun x hx ↦ IsSquare.isSumSq hx)) (fun x hx ↦ ?_)
  induction hx with
  | zero             => exact zero_mem _
  | sq_add a S _ ih  => exact AddSubmonoid.add_mem _ (subset_closure ⟨a, rfl⟩) ih

open AddSubmonoid in
/-- A term of `R` satisfies `IsSumSq` if and only if it can be written as `∑ i ∈ I, x i * x i`. -/
theorem isSumSq_iff_finsum [AddCommMonoid R] [Mul R] (a : R) :
    IsSumSq a ↔
    (∃ (α : Type) (I : Finset α) (x : α → R), a = ∑ i ∈ I, x i * x i) := by
  have : IsSumSq a ↔ a ∈ closure {r : R | IsSquare r} := by simp [closure_isSquare];
  rw [this];
  apply Iff.intro
  case mp  =>
    intro hyp;
    obtain ⟨α, I, y, y_cl, eq⟩ := exists_finset_sum_of_mem_closure hyp;
    exact ⟨α, I, (Classical.epsilon <| fun r => y · = r * r),
      by simpa [eq] using Finset.sum_equiv (Equiv.refl α) (by simp)
                          (Classical.epsilon_spec <| y_cl · ·)⟩
  case mpr =>
    intro hyp; obtain ⟨α,I,y,eq⟩ := hyp;
    simpa [eq] using sum_mem (closure {x : R | IsSquare x})
      (subset_closure <| (by simp : (∀ i ∈ I, y i * y i ∈ _)) · ·)

/-- In a (not necessarily unital) commutative semiring,
if `S1` and `S2` are sums of squares, then `S1 * S2` is a sum of squares. -/
theorem IsSumSq.mul [NonUnitalCommSemiring R] {S1 S2 : R}
    (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 * S2) := by
  rw [isSumSq_iff_finsum] at *;
  obtain ⟨α,I,x,hx⟩ := h1; obtain ⟨β,J,y,hy⟩ := h2;
  rw [hx, hy, Finset.sum_mul_sum, ← Finset.sum_product'];
  refine ⟨_, I ×ˢ J, fun ⟨i,j⟩ => x i * y j, ?_⟩;
  simp [mul_assoc, mul_left_comm]

namespace Subsemiring
variable {T : Type*} [CommSemiring T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : Subsemiring T where
  __ := AddSubmonoid.sumSqIn T
  mul_mem' := IsSumSq.mul
  one_mem' := IsSquare.isSumSq isSquare_one

@[simp] lemma sumSqIn_toAddSubmonoid : (sumSqIn T).toAddSubmonoid = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares
is a sum of squares. -/
theorem IsSumSq.prod [CommSemiring R] {α : Type*} {I : Finset α} {f : α → R}
    (hf : ∀ i ∈ I, IsSumSq <| f i) : IsSumSq (∏ i ∈ I, f i) := by
  simpa using Subsemiring.prod_mem (Subsemiring.sumSqIn R) hf

/--
In a commutative semiring `R`, the subsemiring generated by the squares is the set of
sums of squares in `R`.
-/
theorem Subsemiring.closure_isSquare [CommSemiring R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine le_antisymm (closure_le.2 (fun x hx ↦ IsSquare.isSumSq hx)) (fun x hx ↦ ?_)
  induction hx with
  | zero             => exact zero_mem _
  | sq_add a S _ ih  => exact Subsemiring.add_mem _ (subset_closure ⟨a, rfl⟩) ih

/--
Let `R` be a linearly ordered semiring in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used in
`Mathlib.Algebra.Ring.Semireal.Defs` to show that such semirings are semireal.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : IsSumSq S) : 0 ≤ S := by
  induction pS with
  | zero             => simp only [le_refl]
  | sq_add x S _ ih  => apply add_nonneg (mul_self_nonneg x) ih
