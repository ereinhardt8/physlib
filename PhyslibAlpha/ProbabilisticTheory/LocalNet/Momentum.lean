/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.State
public import PhyslibAlpha.CondensedMatter.Crystal.MomentumSectors

/-!

# Conserved momentum in a represented system

A dynamics commuting with the symmetry acts separately on each momentum sector.

## i. Overview

If the translations of a crystal are realised on its state space, then a time evolution that
commutes with translations conserves crystal momentum: it carries a vector of crystal momentum `k`
to a vector of crystal momentum `k`. For infinite crystals there are in general no normalizable
vectors of definite momentum, so one also needs the momentum *fiber*, the space modulo the
differences `β g v - χ g v`, on which every commuting dynamics acts. Both statements are purely
algebraic and need no analysis. Forgetting positivity, the symmetry of a covariant representation
is a linear action on the big system, and everything of `CondensedMatter.Momentum` applies.

## ii. Key results

- `CovariantNetRepresentation.linearAction` : the translations as linear maps of the big system.
- `CovariantNetRepresentation.isEquivariant_of_commute` : a dynamics commuting with the symmetry.
- `CovariantNetRepresentation.mapsTo_sector` : conservation of momentum.
- `CovariantNetRepresentation.fiberMap` : the dynamics in each momentum fiber.

## iii. Table of contents

- A. The linear action
- B. Dynamics commuting with the symmetry

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.
* F. Bloch, Über die Quantenmechanik der Elektronen in Kristallgittern, Z. Phys. 52 (1929).

-/

@[expose] public section

namespace ProbabilisticTheory

open CondensedMatter

namespace CovariantNetRepresentation

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  {G : Type*} [Group G] [MulAction G R] [RegionAction G R] {N : LocalNet R A}
  {α : NetAction G N} {B : Type*} [OrderUnitSpace B] (ρ : CovariantNetRepresentation α B)

/-!

## A. The linear action

-/

/-- The symmetry action on the target, forgetting positivity: a linear representation of `G`. -/
noncomputable def linearAction : G →* Module.End ℝ B where
  toFun g := (ρ.β g).1.toLinearMap
  map_one' := LinearMap.ext fun x => by
    show (ρ.β 1).1 x = x
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => by
    show (ρ.β (g * h)).1 x = (ρ.β g).1 ((ρ.β h).1 x)
    rw [map_mul]; rfl

@[simp] lemma linearAction_apply (g : G) (b : B) : ρ.linearAction g b = (ρ.β g).1 b := rfl

/-!

## B. Dynamics commuting with the symmetry

-/

/-- A channel commutes with the symmetry when applying it and translating can be done in
either order. -/
def Commutes (D : Channel B B) : Prop := ∀ (g : G) (b : B), D ((ρ.β g).1 b) = (ρ.β g).1 (D b)

lemma commutes_id : ρ.Commutes (.id ℝ B) := fun _ _ => rfl

lemma Commutes.comp {D D' : Channel B B} (hD : ρ.Commutes D) (hD' : ρ.Commutes D') :
    ρ.Commutes (D.comp D') := fun g b => by
  show D (D' _) = _
  rw [hD' g b, hD g]
  rfl

/-- A channel of the target commuting with the symmetry is an equivariant linear map. -/
lemma isEquivariant_of_commute {D : Channel B B}
    (hD : ∀ (g : G) (b : B), D ((ρ.β g).1 b) = (ρ.β g).1 (D b)) :
    Crystal.IsEquivariant ρ.linearAction ρ.linearAction D.toLinearMap :=
  fun g b => hD g b

/-- Symmetric dynamics preserves every momentum sector of the target. -/
lemma mapsTo_sector {D : Channel B B}
    (hD : ∀ (g : G) (b : B), D ((ρ.β g).1 b) = (ρ.β g).1 (D b)) (χ : G → ℝ) {b : B}
    (hb : b ∈ Crystal.sector ρ.linearAction χ) : D b ∈ Crystal.sector ρ.linearAction χ :=
  (ρ.isEquivariant_of_commute hD).mapsTo_sector hb

/-- Symmetric dynamics descends to every momentum fiber of the target. -/
noncomputable def fiberMap {D : Channel B B}
    (hD : ∀ (g : G) (b : B), D ((ρ.β g).1 b) = (ρ.β g).1 (D b)) (χ : G → ℝ) :
    Crystal.Fiber ρ.linearAction χ →ₗ[ℝ] Crystal.Fiber ρ.linearAction χ :=
  (ρ.isEquivariant_of_commute hD).fiberMap χ

end CovariantNetRepresentation

end ProbabilisticTheory
