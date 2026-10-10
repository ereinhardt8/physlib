/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Lattice
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Momentum
public import PhyslibAlpha.CondensedMatter.Crystal.BlochTheorem
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!

# Bloch's theorem

A translation-invariant linear map on a unit-cell sector reduces to a map at each crystal momentum.

## i. Overview

In a crystal the laws of motion are invariant under translations of the lattice. Bloch showed
that the stationary states can then be labelled by a crystal momentum `k`, and that within one
momentum the problem reduces to the finitely many degrees of freedom of a unit cell. Here is the
statement in an algebraic form that needs no Hilbert space and no finiteness.

Let the lattice translations form an abelian group `Λ`, let `M` describe the degrees of freedom of
one unit cell (orbitals, spin components), and suppose the translation-invariant part of the system
is the configurations of unit cells over the lattice, `Λ →₀ M`, with translation acting by moving
configurations. This is a `UnitCellStructure`. The crystal momentum `k` is a character `χ` of
`Λ`, `χ n = exp (i k n)` for a chain, and the *Fourier transform* `ev χ` of a configuration
`ψ` is `∑ m, χ m • ψ m`. Then:

* a linear map commuting with translations acts on Fourier evaluations through a map on the
  unit cell, its *Bloch map* `D(k)`: `ev χ (D ψ) = D(k) (ev χ ψ)`;
* the Bloch matrix of a composite evolution is the product of the Bloch matrices;
* for hopping dynamics with amplitudes `t n` to the cell displaced by `n`, the Bloch matrix is
  `H(k) = ∑ n, exp (i k n) t n`, the Fourier transform of the hopping amplitudes.

The unit-cell identification must be supplied for a translation-invariant sector of the represented
net. The whole observable space need not have this form. A real sector can be complexified to
use complex characters. A finite-dimensional cell makes the Bloch map a matrix; identifying it as
a band Hamiltonian requires a Hamiltonian and its additional structure. No band energies or spectral
decomposition are proved here.

## ii. Key results

- `CovariantNetRepresentation.complexLinearAction` : translations on the complexified system.
- `blochMatrix` : the Bloch map of a translation-invariant linear map.
- `ev_symm_apply` : Bloch's theorem, the evolution in a momentum sector is `H(k)`.
- `blochMatrix_comp` : the Bloch map of a composite linear map is the product.
- `blochMatrix_hopping` : `H(k)` for hopping dynamics is the Fourier transform of the hoppings.
- `UnitCellStructure.complexify` : passing to complex momenta.

## iii. Table of contents

- A. Complexification
- B. Unit-cell structure and Bloch matrices
- C. Hopping dynamics
- D. Complex characters
- E. Grouping sites into unit cells

## iv. References

* F. Bloch, Über die Quantenmechanik der Elektronen in Kristallgittern, Z. Phys. 52 (1929).
* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.

-/

@[expose] public section

namespace ProbabilisticTheory

open CondensedMatter

open scoped TensorProduct

/-!

## A. Complexification

-/

section Complexification

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  {G : Type*} [Group G] [MulAction G R] [RegionAction G R] {N : LocalNet R A}
  {α : NetAction G N} {B : Type*} [OrderUnitSpace B] (ρ : CovariantNetRepresentation α B)

/-- The linear action of the symmetry group on the complexified target `ℂ ⊗ B`. -/
noncomputable def CovariantNetRepresentation.complexLinearAction :
    G →* Module.End ℂ (ℂ ⊗[ℝ] B) where
  toFun g := (ρ.linearAction g).baseChange ℂ
  map_one' := by
    rw [map_one]; exact LinearMap.baseChange_id
  map_mul' g h := by
    rw [map_mul, LinearMap.baseChange_mul]

/-- A channel commuting with the symmetry has a complex-linear extension commuting with the
complexified action. -/
lemma CovariantNetRepresentation.isEquivariant_complex {D : Channel B B}
    (hD : ρ.Commutes D) :
    Crystal.IsEquivariant ρ.complexLinearAction ρ.complexLinearAction
      (D.toLinearMap.baseChange ℂ) := by
  intro g x
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    simp only [CovariantNetRepresentation.complexLinearAction,
      CovariantNetRepresentation.linearAction, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.baseChange_tmul]
    exact congrArg (c ⊗ₜ[ℝ] ·) (hD g b)
  | add x y hx hy => simp only [map_add, hx, hy]

end Complexification

/-!

## B. Unit-cell structure and Bloch matrices

-/

section UnitCell

variable {Λ K M V : Type*} [AddCommGroup Λ] [CommRing K] [AddCommGroup M] [Module K M]
  [AddCommGroup V] [Module K V] (β : Multiplicative Λ →* Module.End K V)

/-- A unit-cell structure: an identification of `V` with configurations of unit cells `M` over `Λ`
that turns translation of configurations into the action `β`. -/
structure UnitCellStructure (M : Type*) [AddCommGroup M] [Module K M] where
  /-- The identification. -/
  Φ : (Λ →₀ M) ≃ₗ[K] V
  /-- It intertwines translation with the action. -/
  Φ_translation : ∀ (a : Multiplicative Λ) (ψ : Λ →₀ M),
    Φ (Crystal.translation (K := K) a ψ) = β a (Φ ψ)

variable {β} (U : UnitCellStructure β M)

/-- A linear map on `V`, read through the unit-cell identification. -/
noncomputable def UnitCellStructure.conj (D : V →ₗ[K] V) : (Λ →₀ M) →ₗ[K] (Λ →₀ M) :=
  U.Φ.symm.toLinearMap ∘ₗ D ∘ₗ U.Φ.toLinearMap

lemma UnitCellStructure.symm_action (a : Multiplicative Λ) (v : V) :
    U.Φ.symm (β a v) = Crystal.translation (K := K) a (U.Φ.symm v) := by
  apply U.Φ.injective
  rw [U.Φ_translation, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Maps commuting with the action are equivariant for translation after reading through `Φ`. -/
lemma UnitCellStructure.isEquivariant_conj {D : V →ₗ[K] V}
    (hD : Crystal.IsEquivariant β β D) :
    Crystal.IsEquivariant (Crystal.translation (K := K) (Λ := Λ) (M := M))
      (Crystal.translation (K := K)) (U.conj D) := by
  intro a ψ
  simp only [UnitCellStructure.conj, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [U.Φ_translation, hD a, U.symm_action]

/-- The Bloch matrix of a map commuting with the action, at a character `χ`. -/
noncomputable def blochMatrix (χ : AddChar Λ K) (D : V →ₗ[K] V) : M →ₗ[K] M :=
  Crystal.symbol χ (U.conj D)

/-- **The Bloch relation.** Fourier evaluation of a configuration read from `V` intertwines a map
commuting with the action with its Bloch matrix. -/
theorem UnitCellStructure.ev_symm_apply {D : V →ₗ[K] V}
    (hD : Crystal.IsEquivariant β β D) (χ : AddChar Λ K) (v : V) :
    Crystal.ev χ (U.Φ.symm (D v))
      = blochMatrix U χ D (Crystal.ev χ (U.Φ.symm v)) := by
  have h := Crystal.ev_apply (U.isEquivariant_conj hD) χ (U.Φ.symm v)
  have e : U.conj D (U.Φ.symm v) = U.Φ.symm (D v) := by simp [UnitCellStructure.conj]
  rw [e] at h
  exact h

/-- The Bloch matrix is multiplicative on maps commuting with the action. -/
lemma blochMatrix_comp {D₁ D₂ : V →ₗ[K] V} (h₁ : Crystal.IsEquivariant β β D₁)
    (χ : AddChar Λ K) :
    blochMatrix U χ (D₁ ∘ₗ D₂) = blochMatrix U χ D₁ ∘ₗ blochMatrix U χ D₂ := by
  have : U.conj (D₁ ∘ₗ D₂) = U.conj D₁ ∘ₗ U.conj D₂ := by
    exact LinearMap.ext fun ψ => by simp [UnitCellStructure.conj]
  rw [blochMatrix, this, Crystal.symbol_comp (U.isEquivariant_conj h₁)]
  rfl

/-!

## C. Hopping dynamics

-/

/-- Dynamics given by hopping matrices `H` between unit cells, transported to `V`. -/
noncomputable def UnitCellStructure.hopping (H : Λ →₀ (M →ₗ[K] M)) : V →ₗ[K] V :=
  U.Φ.toLinearMap ∘ₗ Crystal.hopping H ∘ₗ U.Φ.symm.toLinearMap

lemma UnitCellStructure.isEquivariant_hopping (H : Λ →₀ (M →ₗ[K] M)) :
    Crystal.IsEquivariant β β (U.hopping H) := by
  intro a v
  simp only [UnitCellStructure.hopping, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [U.symm_action, Crystal.isEquivariant_hopping H a, U.Φ_translation]

/-- **Bloch Hamiltonian.** The Bloch matrix of hopping dynamics with hopping matrices `H n` is
`∑ n, χ n • H n`. -/
theorem blochMatrix_hopping (χ : AddChar Λ K) (H : Λ →₀ (M →ₗ[K] M)) :
    blochMatrix U χ (U.hopping H) = H.sum fun n Hn => χ n • Hn := by
  have : U.conj (U.hopping H) = Crystal.hopping H := by
    exact LinearMap.ext fun ψ => by
      simp [UnitCellStructure.conj, UnitCellStructure.hopping]
  rw [blochMatrix, this, Crystal.symbol_hopping]

/-!

## D. Complex characters

-/

section Complexify

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {β : Multiplicative Λ →* Module.End ℝ V}

/-- The complexified action on `ℂ ⊗ V`. -/
noncomputable def complexAction (β : Multiplicative Λ →* Module.End ℝ V) :
    Multiplicative Λ →* Module.End ℂ (ℂ ⊗[ℝ] V) where
  toFun a := (β a).baseChange ℂ
  map_one' := by rw [map_one]; exact LinearMap.baseChange_id
  map_mul' a b := by rw [map_mul, LinearMap.baseChange_mul]

/-- A map commuting with the action has a complex-linear extension commuting with the
complexified action. -/
lemma isEquivariant_baseChange {D : V →ₗ[ℝ] V} (hD : Crystal.IsEquivariant β β D) :
    Crystal.IsEquivariant (complexAction β) (complexAction β) (D.baseChange ℂ) := by
  intro a x
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    simp only [complexAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.baseChange_tmul]
    exact congrArg (c ⊗ₜ[ℝ] ·) (hD a v)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A unit-cell structure with one real mode per cell complexifies to one with one complex mode
per cell, so the Bloch theory applies at complex characters. -/
noncomputable def UnitCellStructure.complexify [DecidableEq Λ] (U : UnitCellStructure β ℝ) :
    UnitCellStructure (complexAction β) ℂ where
  Φ := (TensorProduct.finsuppScalarRight ℝ ℂ ℂ Λ).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) U.Φ
  Φ_translation a ψ := by
    induction ψ using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single x c =>
      rw [Crystal.translation_single]
      simp only [LinearEquiv.trans_apply, TensorProduct.finsuppScalarRight_symm_apply_single,
        TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
      simp only [complexAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.baseChange_tmul]
      rw [← U.Φ_translation, Crystal.translation_single]

end Complexify

end UnitCell

/-!

## E. Grouping sites into unit cells

-/

section Regroup

variable {Λ B K M V : Type*} [AddCommGroup Λ] [AddCommGroup B] [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup V] [Module K V]

/-- Translations between cells leave the internal site label unchanged. -/
def cellTranslations : Multiplicative Λ →* Multiplicative (Λ × B) where
  toFun a := Multiplicative.ofAdd (Multiplicative.toAdd a, 0)
  map_one' := rfl
  map_mul' _ _ := by simp [← ofAdd_add]

/-- Grouping configurations by the first coordinate intertwines the cell translation actions. -/
lemma uncurry_translation (a : Multiplicative Λ) (ψ : Λ →₀ B →₀ M) :
    Finsupp.uncurry (Crystal.translation (K := K) a ψ) =
      Crystal.translation (K := K) (cellTranslations (B := B) a) (Finsupp.uncurry ψ) := by
  change (Finsupp.curryLinearEquiv K).symm (Crystal.translation a ψ) =
    Crystal.translation (cellTranslations a) ((Finsupp.curryLinearEquiv K).symm ψ)
  induction ψ using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n v =>
    induction v using Finsupp.induction_linear with
    | zero => simp only [Finsupp.single_zero, map_zero]
    | add f g hf hg => simp only [Finsupp.single_add, map_add, hf, hg]
    | single b m =>
      change Finsupp.uncurry
        (Crystal.translation (K := K) a (Finsupp.single n (Finsupp.single b m))) =
        Crystal.translation (K := K) (cellTranslations a)
          (Finsupp.uncurry (Finsupp.single n (Finsupp.single b m)))
      simp [Crystal.translation_single, Finsupp.uncurry_single, cellTranslations]

/-- Regrouping a site-based sector produces a unit cell containing all internal site labels. -/
noncomputable def UnitCellStructure.regroup
    {β : Multiplicative (Λ × B) →* Module.End K V} (U : UnitCellStructure β M) :
    UnitCellStructure (β.comp (cellTranslations (Λ := Λ) (B := B))) (B →₀ M) where
  Φ := (Finsupp.curryLinearEquiv K).symm ≪≫ₗ U.Φ
  Φ_translation a ψ := by
    change U.Φ (Finsupp.uncurry (Crystal.translation a ψ)) =
      β (cellTranslations a) (U.Φ (Finsupp.uncurry ψ))
    rw [uncurry_translation, U.Φ_translation]

end Regroup

end ProbabilisticTheory
