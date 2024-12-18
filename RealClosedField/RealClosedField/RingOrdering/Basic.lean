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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith

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

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R]

def RingPreorderingClass.toRingPreordering (P : S) : RingPreordering R where
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

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] {P : S}

/-
## Basic properties
-/

namespace RingPreordering

@[aesop safe 2 apply (rule_sets := [SetLike])]
/- There is no neg_mem -/
lemma neg_mul_mem_of_mem {x y : R} (hx : x ∈ P) (hy : -y ∈ P) : -(x * y) ∈ P := by
  simpa using mul_mem hx hy

@[aesop safe 2 apply (rule_sets := [SetLike])]
/- There is no neg_mem -/
lemma neg_mul_mem_of_neg_mem {x y : R} (hx : -x ∈ P) (hy : y ∈ P) : -(x * y) ∈ P := by
  simpa using mul_mem hx hy

@[aesop safe apply (rule_sets := [SetLike])]
theorem inv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  rw [show (↑a⁻¹ : R) = a * (a⁻¹ * a⁻¹) by simp]
  aesop (config := { enableSimp := false })

@[aesop safe apply (rule_sets := [SetLike])]
theorem Field.inv_mem {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F]
    {P : S} {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  rw [show a⁻¹ = a * (a⁻¹ * a⁻¹) by field_simp]
  aesop

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
    (c : Set (RingPreordering R)) (hcc : IsChain (· ≤ ·) c) (hc : c.Nonempty) : BddAbove c :=
  ⟨mk (sSup (toSubsemiring '' c))
    (fun x => CompleteLattice.le_sSup _ hc.some.toSubsemiring (by aesop (add hc.some_mem safe))
              (by simpa using (hc.some.square_mem' x)))
    (by
      have a : ∀ x ∈ (toSubsemiring '' c), -1 ∉ x := fun P' hP' => by
        obtain ⟨P, _, rfl⟩ := (by aesop : ∃ x ∈ c, x.toSubsemiring = P')
        simpa using P.minus_one_not_mem'
      simp_all [Subsemiring.coe_sSup_of_directedOn (by simp [hc])
        (IsChain.directedOn (IsChain.image _ _ _ (by aesop) hcc))]),
  fun _ _ => by simpa using CompleteLattice.le_sSup (toSubsemiring '' c) _ (by aesop)⟩

end RingPreordering

/-
## Support
-/

namespace AddSubgroup

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

namespace RingPreordering

variable (P) in
class HasIdealSupport : Prop where
  smul_mem_support' (x : R) {a : R} (ha : a ∈ AddSubgroup.preordering_support P) :
    x * a ∈ AddSubgroup.preordering_support P

namespace HasIdealSupport

variable (P) in
/-- Technical lemma to get P as explicit argument -/
lemma smul_mem_support [RingPreordering.HasIdealSupport P] :
    ∀ (x : R) {a : R}, a ∈ AddSubgroup.preordering_support P →
      x * a ∈ AddSubgroup.preordering_support P :=
  HasIdealSupport.smul_mem_support' (P := P)

theorem smul_mem [RingPreordering.HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  have := smul_mem_support P
  simp_all

theorem neg_smul_mem [RingPreordering.HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  have := smul_mem_support P
  simp_all

theorem hasIdealSupport
    (h : ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P) : HasIdealSupport P where
  smul_mem_support' := by simp_all

end RingPreordering.HasIdealSupport

namespace Ideal

variable [RingPreordering.HasIdealSupport P]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def preordering_support : Ideal R where
  __ := AddSubgroup.preordering_support P
  smul_mem' := by simpa using RingPreordering.HasIdealSupport.smul_mem_support P

@[simp] lemma mem_support : x ∈ preordering_support P ↔ x ∈ P ∧ -x ∈ P := Iff.rfl
@[simp, norm_cast] lemma coe_support : preordering_support P = {x : R | x ∈ P ∧ -x ∈ P} := rfl

end Ideal

theorem RingPreordering.hasIdealSupport_of_isUnit_2 (isUnit_2 : IsUnit (2 : R)) :
    RingPreordering.HasIdealSupport P := by
  refine HasIdealSupport.hasIdealSupport (fun x a h₁a h₂a => ?_)
  obtain ⟨half, h2⟩ := IsUnit.exists_left_inv isUnit_2
  let y := (1 + x) * half
  let z := (1 - x) * half
  have mem : (y * y) * a + (z * z) * (-a) ∈ P ∧ (y * y) * (-a) + (z * z) * a ∈ P := by aesop
  rw [show x = y * y - z * z by linear_combination (-(2 * x * half) - 1 * x) * h2]
  ring_nf at mem ⊢
  assumption

/-
## (Prime) orderings
-/

namespace RingPreordering

section IsOrdering

variable (P) in
/-- An ordering `P` on a ring `R` is a preordering such that, for every `x` in `R`,
either `x` or `-x` lies in `P`. -/
class IsOrdering : Prop where
  mem_or_neg_mem' (x : R) : x ∈ P ∨ -x ∈ P

variable [IsOrdering P]

variable (P) in
/-- Technical lemma to get P as explicit argument -/
lemma mem_or_neg_mem : ∀ x : R, x ∈ P ∨ -x ∈ P := IsOrdering.mem_or_neg_mem' (P := P)

@[aesop unsafe apply]
lemma neg_mem_of_not_mem (x : R) (h : x ∉ P) : -x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

@[aesop unsafe apply]
lemma mem_of_not_neg_mem (x : R) (h : -x ∉ P) : x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

instance hasIdealSupport : HasIdealSupport P where
  smul_mem_support' x a ha := by
    cases mem_or_neg_mem P x with
    | inl => aesop
    | inr hx => simpa using ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

end IsOrdering

variable (P) in
/-- A prime ordering `P` on a ring `R` is an ordering whose support is a prime ideal. -/
class IsPrimeOrdering : Prop where
  mem_or_neg_mem' (x : R) : x ∈ P ∨ -x ∈ P
  mem_or_mem' {x y : R} (h : x * y ∈ AddSubgroup.preordering_support P) :
    x ∈ AddSubgroup.preordering_support P ∨ y ∈ AddSubgroup.preordering_support P

instance isOrdering [IsPrimeOrdering P] :
    IsOrdering P where
  mem_or_neg_mem' := IsPrimeOrdering.mem_or_neg_mem'

instance preordering_support_isPrime [IsPrimeOrdering P] :
    (Ideal.preordering_support P).IsPrime where
  ne_top' h := minus_one_not_mem P (by aesop : 1 ∈ Ideal.preordering_support P).2
  mem_or_mem' := IsPrimeOrdering.mem_or_mem'

instance isPrimeOrdering_of_isOrdering
    [IsOrdering P] [(Ideal.preordering_support P).IsPrime] : IsPrimeOrdering P where
  mem_or_neg_mem' := mem_or_neg_mem P
  mem_or_mem' := Ideal.IsPrime.mem_or_mem (by assumption)

theorem isPrimeOrdering_iff :
    IsPrimeOrdering P ↔ (∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P) := by
  refine Iff.intro (fun prime a b h₁ => ?_) (fun h => ?_)
  · by_contra h₂
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ Ideal.preordering_support P ∨ b ∈ Ideal.preordering_support P :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all)
    simp_all
  · refine ⟨by aesop, fun {x y} hxy => ?_⟩
    by_contra h₂
    cases (by aesop : x ∈ P ∨ -x ∈ P) with
    | inl =>  have := h (-x) y
              have := h (-x) (-y)
              simp_all
    | inr =>  have := h x y
              have := h x (-y)
              simp_all

end RingPreordering
