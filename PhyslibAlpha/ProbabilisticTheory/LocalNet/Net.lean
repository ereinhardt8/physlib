/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Maps
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Region
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Pushforward

/-!

# Local nets of observables

The observables measurable in each region, and how a measurement in a region is also a measurement
in a larger one.

## i. Overview

Any actual measurement on an extended system takes place in a bounded region. What can be
measured inside a region `X` is a smaller system of observables than what can be measured
everywhere. A *local net* records this: it assigns to every region `X` the observables `A X`
measurable inside `X`, and to every `X ≤ Y` the map `ι` that regards a measurement made in `X` as
a measurement made in `Y`. Regarding a measurement as made in `X` itself changes nothing, and
passing through an intermediate region gives the same result as passing directly. This is the
setting of local quantum physics (Haag and Kastler) and of the quasi-local description of quantum
lattice systems.

The observables of a region are only an ordered real vector space with a unit, the certain
outcome. The same definition therefore covers classical lattice systems, quantum spin systems and
more general probabilistic theories. Nothing is assumed about products of observables, Hilbert
spaces, or the geometry of the regions.

A net is *faithful* when enlarging a region loses nothing: two measurements in `X` that are
distinguishable remain distinguishable in `Y`. A state of a large region determines, by
restriction, the state of every subregion: the marginal.

## ii. Key results

- `LocalNet` : the observables of each region and the maps from smaller to larger regions.
- `LocalNet.IsFaithful` : enlarging a region loses no information.
- `LocalNet.incl_comp_incl_comp` : including through several regions is including directly.
- `LocalNet.mapEffect_incl` : a yes/no measurement in a region is a yes/no measurement in a
  larger one.
- `LocalNet.restrict` : the marginal of a state of a large region on a subregion.
- `LocalNet.restrict_restrict` : marginals of marginals are marginals.

## iii. Table of contents

- A. The structure
- B. Chains of inclusions
- C. Effects
- D. State restriction
- E. Faithfulness

## iv. References

* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. The structure

-/

/-- A local net of order-unit spaces `A X` over a partially ordered set of regions. -/
structure LocalNet (R : Type*) [PartialOrder R] (A : R → Type*)
    [∀ X, OrderUnitSpace (A X)] where
  /-- The inclusion channel for `X ≤ Y`. -/
  incl : ∀ {X Y : R}, X ≤ Y → Channel (A X) (A Y)
  /-- The inclusion along `X ≤ X` is the identity. -/
  incl_refl : ∀ X : R, incl (le_refl X) = .id ℝ (A X)
  /-- Inclusion along `X ≤ Z` factors through any intermediate `Y`. -/
  incl_trans : ∀ {X Y Z : R} (h₁ : X ≤ Y) (h₂ : Y ≤ Z),
    incl (h₁.trans h₂) = (incl h₂).comp (incl h₁)

namespace LocalNet

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  (N : LocalNet R A) {W X Y Z : R}

@[simp] lemma incl_refl_apply (a : A X) : N.incl (le_refl X) a = a := by
  rw [N.incl_refl]; rfl

lemma incl_trans_apply (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (a : A X) :
    N.incl (h₁.trans h₂) a = N.incl h₂ (N.incl h₁ a) := by
  rw [N.incl_trans]; rfl

/-- Any two proofs of `X ≤ Y` give the same inclusion. -/
lemma incl_proof_irrel (h h' : X ≤ Y) : N.incl h = N.incl h' := rfl

/-!

## B. Chains of inclusions

-/

/-- Inclusion along a chain of three steps equals the direct inclusion. -/
lemma incl_comp_incl_comp (h₁ : W ≤ X) (h₂ : X ≤ Y) (h₃ : Y ≤ Z) :
    (N.incl h₃).comp ((N.incl h₂).comp (N.incl h₁))
      = N.incl ((h₁.trans h₂).trans h₃) := by
  rw [N.incl_trans (h₁.trans h₂) h₃, N.incl_trans h₁ h₂]

lemma incl_comp_incl (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    (N.incl h₂).comp (N.incl h₁) = N.incl (h₁.trans h₂) := (N.incl_trans h₁ h₂).symm

/-!

## C. Effects

-/

/-- Inclusion carries effects to effects. -/
def mapEffect (h : X ≤ Y) (e : Effect (A X)) : Effect (A Y) := (N.incl h).mapEffect e

@[simp] lemma coe_mapEffect (h : X ≤ Y) (e : Effect (A X)) :
    (N.mapEffect h e : A Y) = N.incl h e := rfl

lemma mapEffect_trans (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (e : Effect (A X)) :
    N.mapEffect (h₁.trans h₂) e = N.mapEffect h₂ (N.mapEffect h₁ e) :=
  Subtype.ext (N.incl_trans_apply h₁ h₂ e)

/-!

## D. State restriction

-/

/-- Restriction of a state on the larger region `Y` to the smaller region `X`. -/
def restrict (h : X ≤ Y) (ω : 𝓢[ℝ, A Y]) : 𝓢[ℝ, A X] := ω.comp (N.incl h)

@[simp] lemma restrict_apply (h : X ≤ Y) (ω : 𝓢[ℝ, A Y]) (a : A X) :
    N.restrict h ω a = ω (N.incl h a) := rfl

@[simp] lemma restrict_refl (ω : 𝓢[ℝ, A X]) : N.restrict (le_refl X) ω = ω := by
  ext a; simp

/-- Restricting through an intermediate region agrees with restricting directly. -/
lemma restrict_restrict (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (ω : 𝓢[ℝ, A Z]) :
    N.restrict h₁ (N.restrict h₂ ω) = N.restrict (h₁.trans h₂) ω := by
  ext a; simp [N.incl_trans_apply h₁ h₂]

/-!

## E. Faithfulness

-/

/-- A net is faithful when every inclusion is an order embedding. -/
def IsFaithful : Prop := ∀ {X Y : R} (h : X ≤ Y), Channel.IsOrderEmbedding (N.incl h)

lemma IsFaithful.injective {N : LocalNet R A} (hN : N.IsFaithful) (h : X ≤ Y) :
    Function.Injective (N.incl h) := (hN h).injective

end LocalNet

end ProbabilisticTheory
