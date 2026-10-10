/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Order.Directed
public import Mathlib.Basic.NNReal.Defs

/-!

# Regions of a physical system

Regions ordered by inclusion, with separation and enlargement added only when needed.

## i. Overview

An extended system, such as a crystal, a spin chain or a field in space-time, is studied
through the regions in which it is probed. Regions are ordered by inclusion: `X ≤ Y` means that `X`
lies inside `Y`. Nothing else is required at first: no coordinates, no distance, no notion of
site. Further structure is added separately, only where a theory needs it:

| Capability | Physical meaning | Lean notion |
|---|---|---|
| empty region | no physical support | `OrderBot R` |
| union | measuring in two regions at once | `SemilatticeSup R` |
| directedness | any two regions fit inside a common one | `IsDirected R (· ≤ ·)` |
| separation | disjoint sites, or spacelike separation | `HasSeparation R` |
| enlargement | how far a disturbance can spread | `HasEnlargement R` |

Directedness is what allows one to speak of the whole infinite system, and is not imposed on
every region structure. The enlargement `enlarge r X` of a region is the set of points within
distance `r` of it: a disturbance travelling at speed at most `v` for a time `t` stays inside
`enlarge (v * t) X`.

## ii. Key results

- `HasSeparation` : two regions are separated, symmetrically, and so are their subregions.
- `HasEnlargement` : the neighborhood of a region of a given radius, obeying the triangle
  inequality.

## iii. Table of contents

- A. Separation
- B. Enlargement

## iv. References

* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.
* E. Lieb & D. Robinson, The finite group velocity of quantum spin systems.

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Separation

-/

/-- A separation relation on regions, expressing disjointness or spacelike separation. It is
symmetric and passes to subregions. -/
class HasSeparation (R : Type*) [PartialOrder R] where
  /-- `Sep X Y` says `X` and `Y` are separated. -/
  Sep : R → R → Prop
  /-- Separation is symmetric. -/
  symm : ∀ {X Y : R}, Sep X Y → Sep Y X
  /-- Separation passes to subregions. -/
  mono : ∀ {X Y X' Y' : R}, Sep X Y → X' ≤ X → Y' ≤ Y → Sep X' Y'

namespace HasSeparation

variable {R : Type*} [PartialOrder R] [HasSeparation R] {X Y X' Y' : R}

lemma sep_comm : Sep X Y ↔ Sep Y X := ⟨symm, symm⟩

lemma mono_left (h : Sep X Y) (hX : X' ≤ X) : Sep X' Y := mono h hX le_rfl

lemma mono_right (h : Sep X Y) (hY : Y' ≤ Y) : Sep X Y' := mono h le_rfl hY

end HasSeparation

/-!

## B. Enlargement

-/

/-- Enlargements of regions by a radius, used to state propagation bounds. `enlarge r X` is the
region within distance `r` of `X`. Only the laws that hold for neighborhoods in a metric space are
required: enlarging twice stays within the enlargement by the summed radius, which is the triangle
inequality and not an equality. -/
class HasEnlargement (R : Type*) [PartialOrder R] where
  /-- The enlargement of a region by a radius. -/
  enlarge : NNReal → R → R
  /-- Enlarging by `0` does nothing. -/
  enlarge_zero : ∀ X, enlarge 0 X = X
  /-- Enlarging by `s` and then by `r` stays within enlarging by `r + s`. -/
  enlarge_add_le : ∀ r s X, enlarge r (enlarge s X) ≤ enlarge (r + s) X
  /-- Enlargement is monotone in the region. -/
  enlarge_mono : ∀ r {X Y : R}, X ≤ Y → enlarge r X ≤ enlarge r Y
  /-- Enlargement is monotone in the radius. -/
  enlarge_mono_radius : ∀ {r s : NNReal}, r ≤ s → ∀ X, enlarge r X ≤ enlarge s X

namespace HasEnlargement

variable {R : Type*} [PartialOrder R] [HasEnlargement R]

/-- A region is contained in its enlargement. -/
lemma le_enlarge (r : NNReal) (X : R) : X ≤ enlarge r X := by
  have := enlarge_mono_radius (R := R) (zero_le (a := r)) X
  rwa [enlarge_zero] at this

end HasEnlargement

end ProbabilisticTheory
