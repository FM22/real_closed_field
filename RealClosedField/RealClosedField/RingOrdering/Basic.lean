/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import RealClosedField.RealClosedField.RingOrdering.Defns
import Mathlib.Order.Chain
import Mathlib.Tactic.Ring
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith
import Mathlib.RingTheory.Ideal.Maps

variable {S R : Type*} [CommRing R] [SetLike S R] [RingPreorderingClass S R] {P : S}

/-!
## Preorderings
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

namespace HasIdealSupport

theorem smul_mem [RingPreordering.HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  have := smul_mem_support P
  simp_all

theorem neg_smul_mem [RingPreordering.HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  have := smul_mem_support P
  simp_all

end HasIdealSupport

theorem hasIdealSupport_of_isUnit_2 (isUnit_2 : IsUnit (2 : R)) : HasIdealSupport P := by
  refine hasIdealSupport (fun x a h₁a h₂a => ?_)
  obtain ⟨half, h2⟩ := IsUnit.exists_left_inv isUnit_2
  let y := (1 + x) * half
  let z := (1 - x) * half
  have mem : (y * y) * a + (z * z) * (-a) ∈ P ∧ (y * y) * (-a) + (z * z) * a ∈ P := by aesop
  rw [show x = y * y - z * z by linear_combination (-(2 * x * half) - 1 * x) * h2]
  ring_nf at mem ⊢
  assumption

/- TODO: support always 0 in a field (elementary approach) -/

/-!
## (Prime) orderings
-/

section IsOrdering

variable [IsOrdering P]

@[aesop unsafe apply]
lemma neg_mem_of_not_mem (x : R) (h : x ∉ P) : -x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

@[aesop unsafe apply]
lemma mem_of_not_neg_mem (x : R) (h : -x ∉ P) : x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

instance IsOrdering.hasIdealSupport : HasIdealSupport P where
  smul_mem_support' x a ha := by
    cases mem_or_neg_mem P x with
    | inl => aesop
    | inr hx => simpa using ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

end IsOrdering

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

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-! ## comap -/

/-- The preimage of a preordering along a ring homomorphism is a preordering. -/
def comap (f : A →+* B) (P : RingPreordering B) : RingPreordering A where
  __ := P.toSubsemiring.comap f
  square_mem' x := by have := square_mem P (f x); aesop
  minus_one_not_mem' := by have := minus_one_not_mem P; aesop

@[simp]
theorem coe_comap (P : RingPreordering B) {f : A →+* B} : (P.comap f : Set A) = f ⁻¹' P := rfl

@[simp]
theorem mem_comap {P : RingPreordering B} {f : A →+* B} {x : A} : x ∈ P.comap f ↔ f x ∈ P :=
  Iff.rfl

theorem comap_comap (P : RingPreordering C) (g : B →+* C) (f : A →+* B) :
    (P.comap g).comap f = P.comap (g.comp f) := rfl

instance comap.instIsOrdering (P : RingPreordering B) [IsOrdering P] (f : A →+* B) :
    IsOrdering (comap f P) where
  mem_or_neg_mem' x := by have := mem_or_neg_mem P (f x); aesop

@[simp]
theorem mem_comap_support {P : RingPreordering B} {f : A →+* B} {x : A} :
    x ∈ AddSubgroup.preordering_support (P.comap f) ↔ f x ∈ AddSubgroup.preordering_support P :=
  by simp

@[simp]
theorem comap_support {P : RingPreordering B} {f : A →+* B} :
    AddSubgroup.preordering_support (P.comap f) = (AddSubgroup.preordering_support P).comap f :=
  by ext; simp

instance comap_hasIdealSupport (P : RingPreordering B) [HasIdealSupport P] (f : A →+* B) :
    HasIdealSupport (P.comap f) where
  smul_mem_support' x a ha := by have := smul_mem_support P (f x) (by simpa using ha); simp_all

@[simp]
theorem mem_comap_support' {P : RingPreordering B} [HasIdealSupport P] {f : A →+* B} {x : A} :
    x ∈ Ideal.preordering_support (P.comap f) ↔ f x ∈ Ideal.preordering_support P := by simp

@[simp]
theorem comap_support' {P : RingPreordering B} [HasIdealSupport P] {f : A →+* B} :
    Ideal.preordering_support (P.comap f) = (Ideal.preordering_support P).comap f :=
  by ext; simp

instance comap.instIsPrimeOrdering (P : RingPreordering B) [IsPrimeOrdering P] (f : A →+* B) :
    IsPrimeOrdering (comap f P) := by
  have : (Ideal.preordering_support (P.comap f)).IsPrime := by rw [comap_support']; infer_instance
  infer_instance

/-! ## map -/

/-- The image of a preordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is a subring. -/
def map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P) : RingPreordering B where
  __ := P.toSubsemiring.map f
  square_mem' x := by
    obtain ⟨x', rfl⟩ := hf x
    have := square_mem P x'
    aesop
  minus_one_not_mem' := fun ⟨x', hx', _⟩ => by
    apply minus_one_not_mem P
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    simp_all

@[simp]
theorem coe_map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P) :
    (map hf hsupp : Set B) = f '' P := rfl

@[simp]
theorem mem_map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P) :
    y ∈ map hf hsupp ↔ ∃ x ∈ P, f x = y := Iff.rfl

instance map.instIsOrdering {f : A →+* B} {P : RingPreordering A} [IsOrdering P]
    (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P) :
    IsOrdering (map hf hsupp) where
  mem_or_neg_mem' x := by
    obtain ⟨x', rfl⟩ := hf x
    have := mem_or_neg_mem P x'
    aesop

@[simp]
theorem mem_map_support {f : A →+* B} {P : RingPreordering A} {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P} {x : B} :
    x ∈ AddSubgroup.preordering_support (map hf hsupp) ↔
      ∃ y ∈ AddSubgroup.preordering_support P, f y = x := by
  refine Iff.intro (fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_) (by aesop)
  have : -(a + b) + b ∈ P := by exact add_mem (hsupp (show f (a + b) = 0 by simp_all)).2 hb₁
  aesop

@[simp]
theorem map_support {f : A →+* B} {P : RingPreordering A} {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P} :
    AddSubgroup.preordering_support (map hf hsupp) = (AddSubgroup.preordering_support P).map f :=
  by ext; rw [mem_map_support]; simp

instance map_hasIdealSupport {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P) :
    HasIdealSupport (map hf hsupp) where
  smul_mem_support' x a ha := by
    rw [mem_map_support] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

@[simp]
theorem mem_map_support' {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P} {x : B} :
    x ∈ Ideal.preordering_support (map hf hsupp) ↔
      ∃ y ∈ Ideal.preordering_support P, f y = x := by simp [Ideal.preordering_support]

@[simp]
theorem map_support' {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P} :
    Ideal.preordering_support (map hf hsupp) = (Ideal.preordering_support P).map f := by
  ext; rw [mem_map_support']; refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rcases h with ⟨x', hx', rfl⟩; exact Ideal.mem_map_of_mem f hx'
  · exact Ideal.mem_image_of_mem_map_of_surjective f hf h

instance map.instIsPrimeOrdering {f : A →+* B} {P : RingPreordering A} [IsPrimeOrdering P]
    (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.preordering_support P) :
    IsPrimeOrdering (map hf hsupp) := by
  have : (Ideal.preordering_support (map hf hsupp)).IsPrime := by
    simpa using Ideal.map_isPrime_of_surjective hf (by simpa using hsupp)
  infer_instance

end RingPreordering
