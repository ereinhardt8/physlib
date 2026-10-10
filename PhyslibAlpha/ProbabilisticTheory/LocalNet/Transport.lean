/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Net

/-!

# Identifying equal regions

Bookkeeping that identifies the observables of two regions known to be equal.

## i. Overview

Translating by `h` and then by `g` is translating by `g * h`, and the region `(g * h) • X` is
the same region as `g • (h • X)`. The two expressions are different terms, so the observables
measurable in them have different types. The map `eqIso h : A X ≃ A Y` along `h : X = Y`
identifies them. It is the identity when `h` is `rfl`.

There is no physical content here. This file only keeps the type-theoretic bookkeeping apart, so
that the statements of the symmetry laws elsewhere read as the physical equations.

## ii. Key results

- `eqIso` : identification of the observables of equal regions.
- `eqIso_rfl`, `eqIso_trans`, `eqIso_symm` : identity, composition and inverse of identifications.
- `LocalNet.eqIso_comp_incl` : viewing a measurement in a larger region commutes with the
  identification.
- `LocalNet.restrict_eqIso` : marginals commute with the identification.

## iii. Table of contents

- A. Transport of local systems
- B. Compatibility with inclusions
- C. Compatibility with states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Transport of local systems

-/

section Transport

variable {R : Type*} {A : R → Type*} [∀ X, OrderUnitSpace (A X)] {W X Y Z : R}

/-- The identification of local systems along an equality of regions. -/
def eqIso (h : X = Y) : OrderUnitIso (A X) (A Y) := h ▸ OrderUnitIso.refl (A X)

@[simp] lemma eqIso_rfl : eqIso (A := A) (rfl : X = X) = OrderUnitIso.refl (A X) := rfl

/-- Any two proofs of the same equality give the same identification. -/
lemma eqIso_proof_irrel (h h' : X = Y) : eqIso (A := A) h = eqIso h' := rfl

lemma eqIso_trans (h₁ : X = Y) (h₂ : Y = Z) :
    eqIso (A := A) (h₁.trans h₂) = (eqIso h₁).trans (eqIso h₂) := by
  subst h₁ h₂; rfl

lemma eqIso_symm (h : X = Y) : eqIso (A := A) h.symm = (eqIso h).symm := by
  subst h; rfl

/-- Transport along an equality does not change an observable up to `HEq`. -/
lemma eqIso_apply_heq (h : X = Y) (a : A X) : HEq (eqIso (A := A) h a) a := by
  subst h; rfl

/-- Two observables in the same system have equal transports along the same equality. -/
@[simp] lemma eqIso_apply_rfl (a : A X) : eqIso (A := A) (rfl : X = X) a = a := rfl

end Transport

/-!

## B. Compatibility with inclusions

-/

namespace LocalNet

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  (N : LocalNet R A) {X Y X' Y' : R}

/-- Inclusions agree under transported indices: transporting then including equals including then
transporting. -/
lemma eqIso_comp_incl (hX : X = X') (hY : Y = Y') (h : X ≤ Y) (h' : X' ≤ Y') :
    (eqIso (A := A) hY).toChannel.comp (N.incl h) =
      (N.incl h').comp (eqIso (A := A) hX).toChannel := by
  subst hX hY; rfl

lemma eqIso_incl_apply (hX : X = X') (hY : Y = Y') (h : X ≤ Y) (h' : X' ≤ Y') (a : A X) :
    eqIso (A := A) hY (N.incl h a) = N.incl h' (eqIso (A := A) hX a) := by
  subst hX hY; rfl

/-!

## C. Compatibility with states

-/

lemma restrict_eqIso (hX : X = X') (hY : Y = Y') (h : X ≤ Y) (h' : X' ≤ Y')
    (ω : 𝓢[ℝ, A Y']) :
    N.restrict h ((eqIso (A := A) hY).pullback ω)
      = (eqIso (A := A) hX).pullback (N.restrict h' ω) := by
  subst hX hY; rfl

end LocalNet

end ProbabilisticTheory
