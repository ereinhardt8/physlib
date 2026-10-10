/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.SpinLattice.ClassicalSpins
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!

# The Ising model

The energy of a configuration of Ising spins, its locality, and the Gibbs weights.

## i. Overview

The Ising model describes spins `s i = ±1` on the sites `i` of a lattice. A pair of sites `i`, `j`
interacts with the exchange coupling `J i j`, and each spin feels a longitudinal field `h i`. The
energy of a configuration `c` of the spins in a finite region `Y` is

`E_Y(c) = - (1/2) ∑ i, j ∈ Y, J i j s i s j - ∑ i ∈ Y, h i s i`,

with free boundary conditions: only pairs inside `Y` are counted. Each site has finitely many
interacting neighbors:
site `i` interacts only with the sites in `nbrs i`. A common bound on their geometric distances
is additional data for a finite-range lattice model. In thermal equilibrium at inverse
temperature `β` a finite region is in the Gibbs state, in which the configuration `c` has
probability `exp (- β E_Y(c)) / Z_Y`.

The same energy function defines two models on the same lattice. In the *classical* Ising model
the spins are the numbers `±1` and the observables are functions of the configuration. In the
*quantum* Ising model with the interaction `J i j σᶻ i σᶻ j` the spins are spin-1/2 particles whose
`σᶻ` is `s`, the observables are all operators on the spins, and the Hamiltonian is the operator
that is the multiplication by `E_Y(c)` on the configuration `c`. The two models are related by the
fact that the Gibbs state of the quantum model is the Gibbs probability on the diagonal.

The central property of the energy used later is *locality*: if two configurations agree outside a
region `X`, then the difference of their energies in any region containing the neighbors of `X`
does not depend on that region and is computed from the spins in the neighborhood of `X` alone.
This makes the time evolution of an observable localized in `X` well defined in infinite volume.

## ii. Key results

- `IsingModel` : the exchange couplings, the field, and the range of the interaction.
- `IsingModel.energy` : the energy of a spin configuration in a finite region.
- `IsingModel.energy_sub_energy` : the energy difference of configurations agreeing outside `X`
  is computed in the neighborhood of `X`.
- `IsingModel.weight`, `IsingModel.partition` : Gibbs weights and the partition function.

## iii. Table of contents

- A. The interaction
- B. The energy of a configuration
- C. Locality of energy differences
- D. Gibbs weights

## iv. References

* E. Ising, Beitrag zur Theorie des Ferromagnetismus, Z. Phys. 31 (1925).
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd ed.,
  Section 6.2.
-/

@[expose] public section

namespace CondensedMatter

open SpinLattice

/-!

## A. The interaction

-/

/-- The Ising model on a lattice with sites `S`: the exchange couplings between spins, the
longitudinal field on each spin, and which sites interact with a given site. -/
structure IsingModel (S : Type*) where
  /-- The exchange coupling between the spins at `i` and `j`. -/
  J : S → S → ℝ
  /-- The exchange coupling is symmetric. -/
  J_symm : ∀ i j, J i j = J j i
  /-- The longitudinal field acting on the spin at `i`. -/
  h : S → ℝ
  /-- The sites that interact with the site `i`. -/
  nbrs : S → Finset S
  /-- A site only interacts with its neighbors. -/
  J_support : ∀ i j, J i j ≠ 0 → j ∈ nbrs i

namespace IsingModel

variable {S : Type*} (I : IsingModel S)

/-- The value of a spin, `+1` or `-1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- A region together with all the sites that interact with a site of the region. -/
def plus [DecidableEq S] (X : Finset S) : Finset S := X ∪ X.biUnion I.nbrs

lemma subset_plus [DecidableEq S] (X : Finset S) : X ⊆ I.plus X := Finset.subset_union_left

lemma plus_mono [DecidableEq S] {X Y : Finset S} (h : X ≤ Y) : I.plus X ≤ I.plus Y :=
  Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

lemma nbrs_subset_plus [DecidableEq S] {X : Finset S} {i : S} (hi : i ∈ X) :
    I.nbrs i ⊆ I.plus X :=
  fun _ hj => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hj⟩)

/-!

## B. The energy of a configuration

-/

/-- The energy in a region `Y` of an assignment of spins to all sites, only the spins inside `Y`
being read. -/
noncomputable def energyOf (Y : Finset S) (σ : S → Bool) : ℝ :=
  -(1 / 2) * ∑ i ∈ Y, ∑ j ∈ Y, I.J i j * sgn (σ i) * sgn (σ j) - ∑ i ∈ Y, I.h i * sgn (σ i)

/-- A configuration of the spins in `Y` extended to all sites by `true` outside `Y`. -/
def extend [DecidableEq S] {Y : Finset S} (c : (↥Y → Bool)) : S → Bool :=
  fun s => if hs : s ∈ Y then c ⟨s, hs⟩ else true

/-- The energy of a configuration of the spins in `Y`, with free boundary conditions. -/
noncomputable def energy [DecidableEq S] (Y : Finset S) (c : (↥Y → Bool)) : ℝ :=
  I.energyOf Y (extend c)

lemma energyOf_congr {Y : Finset S} {σ σ' : S → Bool} (h : ∀ s ∈ Y, σ s = σ' s) :
    I.energyOf Y σ = I.energyOf Y σ' := by
  unfold energyOf
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [h i hi, h j hj]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i hi]

/-!

## C. Locality of energy differences

-/

/-- The part of the energy difference of two spin assignments due to the pair `i`, `j`. -/
noncomputable def pairDiff (σ σ' : S → Bool) (i j : S) : ℝ :=
  -(1 / 2) * I.J i j * (sgn (σ i) * sgn (σ j) - sgn (σ' i) * sgn (σ' j))

/-- The part of the energy difference of two spin assignments due to the field at `i`. -/
def fieldDiff (σ σ' : S → Bool) (i : S) : ℝ := I.h i * (sgn (σ i) - sgn (σ' i))

lemma energyOf_sub_energyOf_eq (Y : Finset S) (σ σ' : S → Bool) :
    I.energyOf Y σ - I.energyOf Y σ' =
      ∑ i ∈ Y, ∑ j ∈ Y, I.pairDiff σ σ' i j - ∑ i ∈ Y, I.fieldDiff σ σ' i := by
  unfold energyOf pairDiff fieldDiff
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
  ring

/-- Spin assignments that agree outside `X` have no pair difference unless both sites are
neighbors of `X`. -/
lemma pairDiff_eq_zero [DecidableEq S] {X : Finset S} {σ σ' : S → Bool}
    (hσ : ∀ s ∉ X, σ s = σ' s) {i j : S} (h : i ∉ I.plus X ∨ j ∉ I.plus X) :
    I.pairDiff σ σ' i j = 0 := by
  unfold pairDiff
  by_cases hJ : I.J i j = 0
  · simp [hJ]
  · by_cases hi : i ∈ X
    · exfalso
      have hj : j ∈ I.plus X := I.nbrs_subset_plus hi (I.J_support i j hJ)
      rcases h with h | h
      · exact h (I.subset_plus X hi)
      · exact h hj
    · by_cases hj : j ∈ X
      · exfalso
        have hJ' : I.J j i ≠ 0 := by rwa [I.J_symm]
        have hi' : i ∈ I.plus X := I.nbrs_subset_plus hj (I.J_support j i hJ')
        rcases h with h | h
        · exact h hi'
        · exact h (I.subset_plus X hj)
      · rw [hσ i hi, hσ j hj]; ring

lemma fieldDiff_eq_zero {X : Finset S} {σ σ' : S → Bool} (hσ : ∀ s ∉ X, σ s = σ' s) {i : S}
    (hi : i ∉ X) : I.fieldDiff σ σ' i = 0 := by
  simp [fieldDiff, hσ i hi]

/-- The energy difference of two spin assignments that agree outside `X`, in any region containing
the neighbors of `X`, is computed in the neighborhood of `X` alone. -/
lemma energyOf_sub_energyOf [DecidableEq S] {X Y : Finset S} (hY : I.plus X ⊆ Y)
    {σ σ' : S → Bool} (hσ : ∀ s ∉ X, σ s = σ' s) :
    I.energyOf Y σ - I.energyOf Y σ' =
      I.energyOf (I.plus X) σ - I.energyOf (I.plus X) σ' := by
  rw [energyOf_sub_energyOf_eq, energyOf_sub_energyOf_eq]
  congr 1
  · calc ∑ i ∈ Y, ∑ j ∈ Y, I.pairDiff σ σ' i j
        = ∑ i ∈ I.plus X, ∑ j ∈ Y, I.pairDiff σ σ' i j :=
          (Finset.sum_subset hY fun i _ hi =>
            Finset.sum_eq_zero fun j _ => I.pairDiff_eq_zero hσ (Or.inl hi)).symm
      _ = ∑ i ∈ I.plus X, ∑ j ∈ I.plus X, I.pairDiff σ σ' i j :=
          Finset.sum_congr rfl fun i _ =>
            (Finset.sum_subset hY fun j _ hj => I.pairDiff_eq_zero hσ (Or.inr hj)).symm
  · exact (Finset.sum_subset hY fun i _ hi =>
      I.fieldDiff_eq_zero hσ fun hiX => hi (I.subset_plus X hiX)).symm

lemma energy_sub_energy [DecidableEq S] {X Y : Finset S} (_hXY : X ≤ Y) (hY : I.plus X ≤ Y)
    {c c' : (↥Y → Bool)} (hc : ∀ y : ↥Y, y.1 ∉ X → c y = c' y) :
    I.energy Y c - I.energy Y c' =
      I.energy (I.plus X) (res S Bool hY c) - I.energy (I.plus X) (res S Bool hY c') := by
  unfold energy
  have hσ : ∀ s ∉ X, extend c s = extend c' s := by
    intro s hs
    by_cases hsY : s ∈ Y
    · simp only [extend, hsY, ↓reduceDIte]
      exact hc ⟨s, hsY⟩ hs
    · simp [extend, hsY]
  rw [I.energyOf_sub_energyOf hY hσ]
  have e1 : I.energyOf (I.plus X) (extend c) =
      I.energyOf (I.plus X) (extend (res S Bool hY c)) := by
    refine I.energyOf_congr fun s hs => ?_
    simp [extend, res, hs, hY hs]
  have e2 : I.energyOf (I.plus X) (extend c') =
      I.energyOf (I.plus X) (extend (res S Bool hY c')) := by
    refine I.energyOf_congr fun s hs => ?_
    simp [extend, res, hs, hY hs]
  rw [e1, e2]

/-!

## D. Gibbs weights

-/

/-- The Gibbs weight `exp (- β E)` of a configuration. -/
noncomputable def weight [DecidableEq S] (β : ℝ) (Y : Finset S) (c : (↥Y → Bool)) : ℝ :=
  Real.exp (-β * I.energy Y c)

lemma weight_pos [DecidableEq S] (β : ℝ) (Y : Finset S) (c : (↥Y → Bool)) : 0 < I.weight β Y c :=
  Real.exp_pos _

/-- The partition function of a region. -/
noncomputable def partition [DecidableEq S] (β : ℝ) (Y : Finset S) : ℝ :=
  ∑ c : (↥Y → Bool), I.weight β Y c

lemma partition_pos [DecidableEq S] (β : ℝ) (Y : Finset S) : 0 < I.partition β Y :=
  Finset.sum_pos (fun c _ => I.weight_pos β Y c) ⟨fun _ => true, Finset.mem_univ _⟩

end IsingModel

end CondensedMatter
