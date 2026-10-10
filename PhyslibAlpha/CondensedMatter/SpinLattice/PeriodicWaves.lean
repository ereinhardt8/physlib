/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.SpinLattice.SpinWaves
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!

# Two-component periodic lattice waves

A sector of a classical observable net has two modes per cell and an explicit Bloch dispersion.

## i. Overview

Sites are pairs `(n, b)`, where `n` is an integer cell and `b` is one of two internal labels.
Linear combinations of the local spin observables give a sector of the global classical net.
Grouping by `n` and complexifying identifies it with finite amplitude profiles with two
components per cell. Cell translations act through the net's translation action.

The wave operator is an on-site restoring term plus the discrete Laplacian acting separately on
each component. Its Bloch eigenvalues are `mass b + stiffness * (2 - 2 cos k)`. They are squared
frequencies when used in a second-order wave equation; no time evolution on the full observable
net is asserted. The Bloch relation and the identification of the unit cell are instances of the
general periodic-system framework.

## ii. Key results

- `unitCell`: the two-component sector as an instance of the general unit-cell structure.
- `waveOperator_equivariant`: the wave operator commutes with cell translations.
- `wave_bloch`: Fourier evaluation intertwines the operator with its Bloch map.
- `bloch_eigenmode`: the two internal components are Bloch eigenmodes.
- `band_momentum`: the explicit real dispersion at wavevector `k`.

## iii. Table of contents

- A. The observable sector and unit cell
- B. The periodic wave operator
- C. Bloch eigenmodes and dispersion

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.

-/

@[expose] public section

namespace CondensedMatter.SpinLattice.PeriodicWaves

open ProbabilisticTheory
open scoped TensorProduct

/-- Two internal sites in each integer cell. -/
abbrev Sites := ℤ × ZMod 2

/-- The two complex amplitudes in a cell. -/
abbrev Cell := ZMod 2 →₀ ℂ

/-- Complexified linear spin observables in the classical net on the two-component lattice. -/
abbrev Sector := ℂ ⊗[ℝ] SpinWaves.sector (Λ := Sites)

/-!

## A. The observable sector and unit cell

-/

/-- Cell translations on the observable sector, induced by translations of the local net. -/
noncomputable def cellAction : Multiplicative ℤ →* Module.End ℂ Sector :=
  (complexAction (SpinWaves.actionW (Λ := Sites))).comp
    (cellTranslations (Λ := ℤ) (B := ZMod 2))

/-- The unit-cell identification obtained by grouping actual local spin observables. -/
noncomputable def unitCell : UnitCellStructure cellAction Cell :=
  ((SpinWaves.unitCell (Λ := Sites)).complexify).regroup

/-!

## B. The periodic wave operator

-/

/-- The on-site restoring operator with a separate squared frequency for each component. -/
noncomputable def cellMass (mass : ZMod 2 → ℝ) : Cell →ₗ[ℂ] Cell :=
  Finsupp.lsum ℂ fun b => Finsupp.lsingle b ∘ₗ ((mass b : ℂ) • LinearMap.id)

/-- A two-component wave operator: on-site restoring forces plus the discrete Laplacian. -/
noncomputable def waveOperator (mass : ZMod 2 → ℝ) (stiffness : ℝ) :
    (ℤ →₀ Cell) →ₗ[ℂ] (ℤ →₀ Cell) :=
  Crystal.hop 0 (cellMass mass) + (stiffness : ℂ) •
    ((2 : ℂ) • LinearMap.id - Crystal.hop 1 LinearMap.id - Crystal.hop (-1) LinearMap.id)

/-- The wave operator is homogeneous under cell translations. -/
lemma waveOperator_equivariant (mass : ZMod 2 → ℝ) (stiffness : ℝ) :
    Crystal.IsEquivariant (Crystal.translation (K := ℂ) (Λ := ℤ) (M := Cell))
      (Crystal.translation (K := ℂ)) (waveOperator mass stiffness) := by
  intro g ψ
  simp only [waveOperator, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_add, map_smul, map_sub]
  rw [Crystal.isEquivariant_hop 0 (cellMass mass) g ψ,
    Crystal.isEquivariant_hop 1 LinearMap.id g ψ,
    Crystal.isEquivariant_hop (-1) LinearMap.id g ψ]

/-- The same periodic operator acting on the sector of global observables. -/
noncomputable def sectorWaveOperator (mass : ZMod 2 → ℝ) (stiffness : ℝ) : Sector →ₗ[ℂ] Sector :=
  unitCell.Φ.toLinearMap ∘ₗ waveOperator mass stiffness ∘ₗ unitCell.Φ.symm.toLinearMap

/-- Fourier evaluation of the observable sector intertwines the wave operator with its Bloch map. -/
lemma wave_bloch (mass : ZMod 2 → ℝ) (stiffness : ℝ) (χ : AddChar ℤ ℂ) (v : Sector) :
    Crystal.ev χ (unitCell.Φ.symm (sectorWaveOperator mass stiffness v)) =
      Crystal.symbol χ (waveOperator mass stiffness) (Crystal.ev χ (unitCell.Φ.symm v)) := by
  simpa [sectorWaveOperator] using
    Crystal.ev_apply (waveOperator_equivariant mass stiffness) χ (unitCell.Φ.symm v)

/-!

## C. Bloch eigenmodes and dispersion

-/

/-- The Bloch eigenvalue of a component, interpreted as squared frequency for wave dynamics. -/
noncomputable def band (mass : ZMod 2 → ℝ) (stiffness : ℝ) (χ : AddChar ℤ ℂ) (b : ZMod 2) : ℂ :=
  mass b + stiffness * (2 - χ 1 - χ (-1))

/-- Each of the two internal components is an eigenmode of the Bloch map. -/
lemma bloch_eigenmode (mass : ZMod 2 → ℝ) (stiffness : ℝ) (χ : AddChar ℤ ℂ) (b : ZMod 2) :
    Crystal.symbol χ (waveOperator mass stiffness) (Finsupp.single b 1) =
      band mass stiffness χ b • Finsupp.single b 1 := by
  simp [Crystal.symbol_apply, waveOperator, Crystal.hop, Crystal.translation_single,
    cellMass, band, Finsupp.smul_single]
  ext j
  by_cases he : b = j <;> simp [he]

/-- The lattice character at real wavevector `k`, in lattice units. -/
noncomputable def momentumCharacter (k : ℝ) : AddChar ℤ ℂ where
  toFun n := Complex.exp ((k : ℂ) * n * Complex.I)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The two dispersion branches are real and have the usual discrete-Laplacian cosine form. -/
lemma band_momentum (mass : ZMod 2 → ℝ) (stiffness k : ℝ) (b : ZMod 2) :
    band mass stiffness (momentumCharacter k) b =
      ((mass b + stiffness * (2 - 2 * Real.cos k) : ℝ) : ℂ) := by
  simp [band, momentumCharacter, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  left
  ring

end CondensedMatter.SpinLattice.PeriodicWaves
