/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Ring.Subsemiring.Order

open Set

variable (S R : Type*) [Ring R] [SetLike S R]

class RingOrderingClass extends SubsemiringClass S R : Prop where
  square_mem {P : S} {x : R} : x * x ∈ P
  minus_one_not_mem {P : S} : -1 ∉ P

structure RingOrdering extends Subsemiring R where
  square_mem' {x : R} : x * x ∈ carrier
  minus_one_not_mem' : -1 ∉ carrier

instance RingOrdering.instSetLike : SetLike (RingOrdering R) R where
  coe P := P.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance RingOrdering.instRingOrderingClass : RingOrderingClass (RingOrdering R) R where
  zero_mem {C} := C.zero_mem'
  one_mem {C} := C.one_mem'
  add_mem {C} := C.add_mem'
  mul_mem {C} := C.mul_mem'
  square_mem {C} := C.square_mem'
  minus_one_not_mem {C} := C.minus_one_not_mem'

/- TODO: contruct precone from only add, mul, sq, minus axioms -/

/--
Given a set `P : Set R` in a ring `R`, the property of being a precone is defined as
a `Prop`-valued structure with four fields: stability of `P` under addition and multiplication,
the fact that `P` contains all squares, and the fact that `(-1 : R) ∉ P`.
-/
@[mk_iff]
structure Set.isPrecone.{k} {R : Type k} [Ring R] (P : Set R) : Prop :=
  add   : ∀ {x y : R}, x ∈ P ∧ y ∈ P → x + y ∈ P
  mul   : ∀ {x y : R}, x ∈ P ∧ y ∈ P → x * y ∈ P
  sq    : ∀ {x : R}, x ^ 2 ∈ P
  minus : (-1 : R) ∉ P

/--
We define the type of precones in a ring `R` as dependent pairs consisting of a term `P : Set R` and a proof of the property `P.isPrecone`.
-/
@[ext]
structure PreconeIn.{k} (R : Type k) [Ring R] : Type k :=
  /-- The carrier of a precone is a set in `R`. -/ --#
  carrier : Set R
  ppty    : carrier.isPrecone

/--
We say that a term `x : R` *belongs* to a precone `P` in `R` if it belongs to the underlying set of that precone, i.e. to `P.carrier`.
-/
instance (R : Type _) [Ring R] : Membership R (PreconeIn R) where
  mem x P := x ∈ P.carrier

/-
## Basic properties of precones
-/

theorem zero_in_precone.{k} {R : Type k} [Ring R]
    : (P : PreconeIn R) → 0 ∈ P := by
  intro P
  have aux : (0 : R) ^ 2 ∈ P := isPrecone.sq P.ppty
  rewrite [zero_pow] at aux
  · exact aux
  · exact Ne.symm (Nat.zero_ne_add_one 1)

theorem one_in_precone.{k} {R : Type k} [Ring R]
    : (P : PreconeIn R) → 1 ∈ P := by
  intro P
  have aux : (1 : R) ^ 2 ∈ P := isPrecone.sq P.ppty
  rewrite [one_pow] at aux
  exact aux

/-
## Constructing larger precones
-/

/--
Given a ring `R`, the function `addElem` sends a precone `P` and a term `a` in `R` to the set `P[a] := {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}`. For convenience, we define this function inductively.
-/
inductive addElem.{k} {R : Type k} [Ring R] (P : PreconeIn R) (a : R) : Set R :=
  | intro (x y z : R) (hx : x ∈ P) (hy : y ∈ P) (hz : z = x + a * y) : addElem P a z

/--
We introduce the simpler notation `P[a]` for the set `addElem P a`. In theorem `addElemSet`, this set is shown to be equal to `{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}`.
-/
notation:max P"["a"]" => addElem P a

/-
We prove that the set `P[a]` consists exactly of all terms in `R` that are of the form `x + a * y` for some `x ∈ P` and `y ∈ P`.
-/

theorem addElemSet.{k} {R : Type k} [Ring R] (P : PreconeIn R) (a : R)
    : P[a] = {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y} := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨x, y, u, hx, hy, hu⟩
    apply Exists.intro x
    apply And.intro
    · exact hx
    · apply Exists.intro y
      exact And.intro hy hu
  · intro hu
    rcases hu with ⟨x, hx, y, hy, hu⟩
    exact addElem.intro x y u hx hy hu

/-
Next, we prove that the set `P[a]` contains the underlying set `P.carrier` of the precone `P`. This is so because an element `x ∈ P` can be written as `x + a * 0`, with `0 ∈ P`.
-/

theorem addElem.inclusion.{k} {R : Type k} [Ring R] (P : PreconeIn R) (a : R)
    : P.carrier ⊆ P[a] := by
  intro x hx
  have aux : x = x + a * 0 := by rw [mul_zero, add_zero]
  exact addElem.intro x 0 x hx (zero_in_precone P) aux

/-
We also prove that the set `P[a]` is stable under addition and multiplication. For multiplication, we add the hypothesis that the ring `R` is commutative. These two lemmas are steps in the proof of theorem `addElemToPrecone` below.

More precisely, in theorem `addElemToPrecone`, we show that if `P` is a precone in `R` and if `a : R` satisfies `-a ∉ P`, then `P[a]` is a precone in `R`. We do this by checking the four properties `add`, `mul`, `sq`and `minus` separately, each one in a different lemma.
-/

lemma addElemToPrecone.add.{k} {R : Type k} [Ring R] (P : PreconeIn R) (a : R)
    : ∀ {x y : R}, x ∈ P[a] ∧ y ∈ P[a] → x + y ∈ P[a] := by
  intro x y ⟨hx, hy⟩
  rcases hx with ⟨u, v, x, hu, hv, hx⟩
  rcases hy with ⟨p, q, y, hp, hq, hy⟩
  rw [hx, hy]
  apply addElem.intro (u + p) (v + q) ((u + a * v) + (p + a * q))
  · exact isPrecone.add P.ppty ⟨hu, hp⟩
  · exact isPrecone.add P.ppty ⟨hv, hq⟩
  · rw [add_assoc, ← add_assoc _ p _, add_assoc u _ _, add_comm _ p, mul_add, add_assoc p _ _]
    -- the last identity holds in a non-necessarily commutative ring; in a commutative ring, the `ring` tactic closes the goal

lemma addElemToPrecone.mul.{k} {R : Type k} [CommRing R] (P : PreconeIn R) (a : R)
    : ∀ {x y : R}, x ∈ P[a] ∧ y ∈ P[a] → x * y ∈ P[a] := by
  intro x y ⟨hx, hy⟩
  rcases hx with ⟨u, v, x, hu, hv, hx⟩
  rcases hy with ⟨p, q, y, hp, hq, hy⟩
  rw [hx, hy]
  have aux : (u + a * v) * (p + a * q) = (u * p + a ^ 2 * (v * q)) +  a * (u * q + v * p) := by ring_nf
  apply addElem.intro (u * p + a ^ 2 * (v * q)) ((u * q + v * p)) ((u + a * v) * (p + a * q))
  · apply isPrecone.add P.ppty
    apply And.intro
    · exact isPrecone.mul P.ppty ⟨hu, hp⟩
    · apply isPrecone.mul P.ppty
      apply And.intro
      · exact isPrecone.sq P.ppty
      · exact isPrecone.mul P.ppty ⟨hv, hq⟩
  · apply isPrecone.add P.ppty
    apply And.intro
    · exact isPrecone.mul P.ppty ⟨hu, hq⟩
    · exact isPrecone.mul P.ppty ⟨hv, hp⟩
  · exact aux

/-
Based on that, we set out to find sufficient conditions for `P[a]` to be a precone in `R`. First, we prove that `P[a]` contains all squares in `R` (because they are already in `P` and `P ⊆ P[a]`).
-/

lemma addElemToPrecone.sq.{k} {R : Type k} [Ring R] (P : PreconeIn R) (a : R)
     : ∀ {x : R}, x ^ 2 ∈ P[a] := by
  intro x
  apply addElem.inclusion P a
  exact isPrecone.sq P.ppty

/-
In order to prove that `P[a]` is a precone, the remaining property to show is that `-1 ∉ P[a]`. This holds if we work *in a field* and if `-a ∉ P`. The proof goes as follows.

Assume that `-1 ∈ P[a]`. Then `-1 = x + a * y` for some `x, y ∈ P`. If `y = 0`, then `-1 = x ∈ P`, which implies `False` because `P` is precone. So we have proven that `y ≠ 0` and we can write ` -a = x * y * (1 / y) ^ 2 + y * (1 / y) ^ 2`. Since `P` is precone, it contains all the squares in `R`. And since `P` contains `x` and `y` and is stable under addition and multiplication, it contains `-a`. But by assumption `-a ∈ P → False`, so we have proven `False`. Note that the proof is constructive.
-/

lemma addElemToPrecone.minus.{k} {F : Type k} [Field F] (P : PreconeIn F) (a : F) (ha : -a ∉ P)
    : -1 ∉ P[a] := by
  intro h
  rcases h with ⟨x, y, z, hx, hy, hz⟩
  have hy' : y ≠ 0 := by
    intro h
    apply isPrecone.minus P.ppty
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
  apply isPrecone.add P.ppty
  apply And.intro
  · apply isPrecone.mul P.ppty
    apply And.intro
    · exact isPrecone.mul P.ppty ⟨hx, hy⟩
    · exact isPrecone.sq P.ppty
  · apply isPrecone.mul P.ppty
    apply And.intro
    · exact hy
    · exact isPrecone.sq P.ppty

/-
Putting the previous lemmas together, we can prove that if `F` is a field, `P` is a precone in `F` and `a` is an element of `P` such that `-a ∉ P`, then `P[a]` is a precone in `F`.
-/

theorem addElemToPrecone.{k} {F : Type k} [Field F] (P : PreconeIn F) (a : F) (ha : -a ∉ P)
    : P[a].isPrecone := by
  constructor -- apply isPrecone.mk
  · case add   => exact addElemToPrecone.add P a
  · case mul   => exact addElemToPrecone.mul P a
  · case sq    => exact addElemToPrecone.sq P a
  · case minus => exact addElemToPrecone.minus P a ha

/--
The function `augmentedPrecone` sends a precone `P` in a field `F` and a term `a : F` such that `-a ∉ P` to the precone `P[a]`.
-/
def augmentedPrecone.{k} {F : Type k} [Field F] (P : PreconeIn F) (a : F) (ha : -a ∉ P) :
    PreconeIn F where
  carrier := P[a]
  ppty    := (addElemToPrecone P a ha : P[a].isPrecone)

/-
For future use, we put an ordering on the type of precones in a ring: we say that `P ≤ Q` if `P.carrier ⊆ Q.carrier`.
-/

instance (R : Type _) [Ring R] : LE (PreconeIn R) where
  le P Q := P.carrier ⊆ Q.carrier

-- #lint
