/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import RealClosedField.RealClosedField.RingOrdering.Defns
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

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
        obtain ⟨P, _, rfl⟩ := show ∃ x ∈ c, x.toSubsemiring = P' by simp_all
        simpa using P.minus_one_not_mem'
      simp_all [Subsemiring.coe_sSup_of_directedOn (by simp [hc])
        (IsChain.directedOn (IsChain.image _ _ _ (by aesop) hcc))]),
  fun _ _ => by simpa using CompleteLattice.le_sSup (toSubsemiring '' c) _ (by aesop)⟩

variable (P) in
theorem AddSubgroup.one_not_mem_support : 1 ∉ support P := by
  aesop (add unsafe forward (minus_one_not_mem P))

variable (P) in
theorem AddSubgroup.support_neq_top : support P ≠ ⊤ := fun eq => by
  have : 1 ∉ (⊤ : AddSubgroup R) := by rw[← eq]; exact one_not_mem_support P
  simp_all

variable (P) in
theorem Ideal.one_not_mem_support [HasIdealSupport P] : 1 ∉ support P :=
  AddSubgroup.one_not_mem_support P

variable (P) in
theorem Ideal.support_neq_top [HasIdealSupport P] : support P ≠ ⊤ := fun eq => by
  have : 1 ∉ (⊤ : Ideal R) := by rw[← eq]; exact one_not_mem_support P
  simp_all

namespace HasIdealSupport

theorem smul_mem [HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  have := smul_mem_support P
  simp_all

theorem neg_smul_mem [HasIdealSupport P]
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

theorem support_eq_bot {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] (P : S) :
    AddSubgroup.support P = ⊥ := by
  refine AddSubgroup.ext (fun x => Iff.intro (fun h => ?_) (fun h => by aesop))
  by_contra hz
  apply minus_one_not_mem P
  rw [show -1 = x * (-x)⁻¹ by field_simp [show x ≠ 0 by simp_all]]
  aesop

theorem support_eq_bot' {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] (P : S) :
    AddSubgroup.support P = ⊥ := by
  rcases em <| (2 : F) = 0 with eq | neq
  · refine False.elim <| minus_one_not_mem P ?_
    rw [show (-1 : F) = 1 by linear_combination -eq]
    apply one_mem
  · apply AddSubgroup.ext
    have : HasIdealSupport P := hasIdealSupport_of_isUnit_2 (by aesop)
    have h : Ideal.support P = ⊥ := by
      aesop (add unsafe forward (eq_bot_or_eq_top (Ideal.support P)),
                 unsafe forward (Ideal.support_neq_top P))
    have : ∀ x, x ∈ Ideal.support P ↔ x ∈ (⊥ : Ideal F) := by simp_all
    rcases h with -
    simp_all

/- TODO : decide which proof to use -/

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

instance support_isPrime [IsPrimeOrdering P] :
    (Ideal.support P).IsPrime where
  ne_top' h := minus_one_not_mem P (by aesop : 1 ∈ Ideal.support P).2
  mem_or_mem' := IsPrimeOrdering.mem_or_mem'

instance isPrimeOrdering_of_isOrdering
    [IsOrdering P] [(Ideal.support P).IsPrime] : IsPrimeOrdering P where
  mem_or_neg_mem' := mem_or_neg_mem P
  mem_or_mem' := Ideal.IsPrime.mem_or_mem (by assumption)

theorem isPrimeOrdering_iff :
    IsPrimeOrdering P ↔ (∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P) := by
  refine Iff.intro (fun prime a b h₁ => ?_) (fun h => ?_)
  · by_contra h₂
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ Ideal.support P ∨ b ∈ Ideal.support P :=
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

/-- The preimage of an ordering along a ring homomorphism is an ordering. -/
instance comap.instIsOrdering (P : RingPreordering B) [IsOrdering P] (f : A →+* B) :
    IsOrdering (comap f P) where
  mem_or_neg_mem' x := by have := mem_or_neg_mem P (f x); aesop

@[simp]
theorem mem_comap_support {P : RingPreordering B} {f : A →+* B} {x : A} :
    x ∈ AddSubgroup.support (P.comap f) ↔ f x ∈ AddSubgroup.support P :=
  by simp

@[simp]
theorem comap_support {P : RingPreordering B} {f : A →+* B} :
    AddSubgroup.support (P.comap f) = (AddSubgroup.support P).comap f :=
  by ext; simp

instance comap_hasIdealSupport (P : RingPreordering B) [HasIdealSupport P] (f : A →+* B) :
    HasIdealSupport (P.comap f) where
  smul_mem_support' x a ha := by have := smul_mem_support P (f x) (by simpa using ha); simp_all

@[simp]
theorem mem_comap_support' {P : RingPreordering B} [HasIdealSupport P] {f : A →+* B} {x : A} :
    x ∈ Ideal.support (P.comap f) ↔ f x ∈ Ideal.support P := by simp

@[simp]
theorem comap_support' {P : RingPreordering B} [HasIdealSupport P] {f : A →+* B} :
    Ideal.support (P.comap f) = (Ideal.support P).comap f :=
  by ext; simp

/-- The preimage of a prime ordering along a ring homomorphism is a prime ordering. -/
instance comap.instIsPrimeOrdering (P : RingPreordering B) [IsPrimeOrdering P] (f : A →+* B) :
    IsPrimeOrdering (comap f P) := by
  have : (Ideal.support (P.comap f)).IsPrime := by rw [comap_support']; infer_instance
  infer_instance

/-! ## map -/

/-- The image of a preordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is a preordering. -/
def map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P) : RingPreordering B where
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
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P) :
    (map hf hsupp : Set B) = f '' P := rfl

@[simp]
theorem mem_map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P) :
    y ∈ map hf hsupp ↔ ∃ x ∈ P, f x = y := Iff.rfl

/-- The image of an ordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is an ordering. -/
instance map.instIsOrdering {f : A →+* B} {P : RingPreordering A} [IsOrdering P]
    (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P) :
    IsOrdering (map hf hsupp) where
  mem_or_neg_mem' x := by
    obtain ⟨x', rfl⟩ := hf x
    have := mem_or_neg_mem P x'
    aesop

@[simp↓]
theorem mem_map_support {f : A →+* B} {P : RingPreordering A} {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P} {x : B} :
    x ∈ AddSubgroup.support (map hf hsupp) ↔
      ∃ y ∈ AddSubgroup.support P, f y = x := by
  refine Iff.intro (fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_) (by aesop)
  have : -(a + b) + b ∈ P := by exact add_mem (hsupp (show f (a + b) = 0 by simp_all)).2 hb₁
  aesop

@[simp]
theorem map_support {f : A →+* B} {P : RingPreordering A} {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P} :
    AddSubgroup.support (map hf hsupp) = (AddSubgroup.support P).map f := by
  ext; simp

instance map_hasIdealSupport {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P) :
    HasIdealSupport (map hf hsupp) where
  smul_mem_support' x a ha := by
    rw [mem_map_support] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

@[simp↓]
theorem mem_map_support' {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P} {x : B} :
    x ∈ Ideal.support (map hf hsupp) ↔
      ∃ y ∈ Ideal.support P, f y = x := by simp [Ideal.support]

@[simp]
theorem map_support' {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P} :
    Ideal.support (map hf hsupp) = (Ideal.support P).map f := by
  ext; simp [Ideal.mem_map_iff_of_surjective f hf]

/-- The image of a prime ordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is a prime ordering. -/
instance map.instIsPrimeOrdering {f : A →+* B} {P : RingPreordering A} [IsPrimeOrdering P]
    (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ AddSubgroup.support P) :
    IsPrimeOrdering (map hf hsupp) := by
  have : (Ideal.support (map hf hsupp)).IsPrime := by
    simpa using Ideal.map_isPrime_of_surjective hf (by simpa using hsupp)
  infer_instance

end RingPreordering

/- TODO : specialise to quotient map R ->> R/supp(P) -/
