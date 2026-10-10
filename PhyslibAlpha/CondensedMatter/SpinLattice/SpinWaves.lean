/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.SpinLattice.ClassicalSpins
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Bloch

/-!

# Linear spin observables on a periodic lattice

The linear observables of a spin lattice form a crystal to which Bloch's theorem applies.

## i. Overview

The simplest observable at a site `x` of a lattice of two-state spins is the spin itself,
`s x = ±1`. A linear combination `∑ ψ x • s x` is a weighted spin measurement, with a
coefficient `ψ x` at each site. Its expectation is the same weighted sum of local magnetizations.
Spin observables at different sites are linearly independent, so
these combinations form a space identified with configurations of one real mode per cell,
`Λ →₀ ℝ`, and translating a profile is moving the spin observables.

This is a crystal in the sense of Bloch's theorem. The space of profiles carries the translation
action, and any time evolution of the lattice that commutes with translations and maps profiles to
profiles has a Bloch matrix at every crystal momentum, which is a number here as there is one mode
per cell. For hopping dynamics, in which the amplitude at a site is fed to its neighbours, it is
the Fourier transform of the hopping amplitudes; for a chain with equal amplitude to both nearest
neighbours it is `exp (i k) + exp (-i k) = 2 cos k` in lattice units. Real dynamics is complexified
to treat unimodular characters.

This file constructs a sector of observables and conditional Bloch relations. It does not specify
an Ising dynamics or derive a physical spin-wave dispersion from an interacting model.

## ii. Key results

- `spin` : the spin observable at a site of the infinite lattice.
- `spinMap_injective` : spin observables at different sites are independent.
- `β_spin` : translating the lattice moves the spin observables.
- `unitCell` : linear spin observables have one coefficient per cell.
- `bloch_hopping` : the Bloch Hamiltonian of hopping dynamics on the spin waves.
- `bloch_relation_complex` : the Bloch relation for translation-invariant real dynamics.
- `bloch_nearest_neighbour` : the dispersion `2 cos k` of a nearest-neighbour chain.

## iii. Table of contents

- A. Spin observables
- B. Independence
- C. Translation
- D. The unit-cell structure

## iv. References

* F. Bloch, Über die Quantenmechanik der Elektronen in Kristallgittern, Z. Phys. 52 (1929).
* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.

-/

@[expose] public section

namespace CondensedMatter

namespace SpinLattice

namespace SpinWaves

open ProbabilisticTheory ProbabilisticTheory.GlobalSystem
open scoped Pointwise TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [DecidableEq Λ]

/-- The global system of the classical lattice net with `Bool` spins. -/
abbrev Gl : Type _ := GlobalSystem (net Λ Bool) (isFaithful Λ Bool)

/-!

## A. Spin observables

-/

/-- The spin observable at `x` on the region `X`: `±1` according to the spin at `x`, and `0` when
`x` is outside `X`. -/
def spinObs (X : Finset Λ) (x : Λ) : Obs Λ Bool X :=
  fun c => if h : x ∈ X then (if c ⟨x, h⟩ then 1 else -1) else 0

/-- The spin observable at `x` in the global system. -/
noncomputable def spin (x : Λ) : Gl Λ := ofLoc _ _ ({x} : Finset Λ) (spinObs Λ {x} x)

variable {Λ}

omit [AddCommGroup Λ] in
/-- A spin observable is the same global observable on every region containing its site. -/
lemma ofLoc_spinObs (X : Finset Λ) {x : Λ} (hx : x ∈ X) :
    ofLoc _ _ X (spinObs Λ X x) = spin Λ x := by
  have h : ({x} : Finset Λ) ≤ X := by simpa using hx
  have hincl : (net Λ Bool).incl h (spinObs Λ {x} x) = spinObs Λ X x := by
    funext c
    simp [net, spinObs, res, hx]
    try rfl
  have := ofLoc_incl (N := net Λ Bool) (hN := isFaithful Λ Bool) h (spinObs Λ {x} x)
  rw [hincl] at this
  exact this

/-- The linear map from site-labelled coefficients to spin-wave observables. -/
noncomputable def spinMap : (Λ →₀ ℝ) →ₗ[ℝ] Gl Λ := Finsupp.linearCombination ℝ (spin Λ)

omit [AddCommGroup Λ] in
lemma spinMap_single (x : Λ) (m : ℝ) : spinMap (Finsupp.single x m) = m • spin Λ x := by
  simp [spinMap]

/-!

## B. Independence

-/

omit [AddCommGroup Λ] in
/-- The value of a combination of spin observables at a configuration. -/
lemma sum_spinObs_apply (Y : Finset Λ) (ψ : Λ →₀ ℝ) (c : ↥Y → Bool) :
    (∑ x ∈ Y, ψ x • spinObs Λ Y x) c
      = ∑ x : ↥Y, ψ x.1 * (if c x then 1 else -1) := by
  rw [Finset.sum_apply]
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [spinObs, x.2]

omit [AddCommGroup Λ] in
/-- Spin observables at distinct sites are linearly independent in the global system. -/
lemma spinMap_injective : Function.Injective (spinMap (Λ := Λ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  have hsum : spinMap ψ = ofLoc (net Λ Bool) (isFaithful Λ Bool) ψ.support
      (∑ x ∈ ψ.support, ψ x • spinObs Λ ψ.support x) := by
    rw [spinMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [map_smul, ofLoc_spinObs ψ.support hx]
  rw [hsum] at hψ
  have hF : (∑ x ∈ ψ.support, ψ x • spinObs Λ ψ.support x) = 0 :=
    ofLoc_injective (N := net Λ Bool) (hN := isFaithful Λ Bool) ψ.support
      (hψ.trans (map_zero _).symm)
  ext x₀
  by_cases hx₀ : x₀ ∈ ψ.support
  · have hp := sum_spinObs_apply ψ.support ψ (fun _ => true)
    have hm := sum_spinObs_apply ψ.support ψ (fun y => decide (y.1 ≠ x₀))
    rw [hF] at hp hm
    have h := sub_eq_zero.2 (hp.symm.trans hm)
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (⟨x₀, hx₀⟩ : ↥ψ.support)] at h
    · simp at h
      simpa using h
    · intro y _ hy
      have : y.1 ≠ x₀ := fun e => hy (Subtype.ext e)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simpa using Finsupp.notMem_support_iff.1 hx₀

/-!

## C. Translation

-/

/-- The net action of translations on the classical lattice net. -/
abbrev act : NetAction (Multiplicative Λ) (net Λ Bool) := netAction Λ Bool (Multiplicative Λ)

/-- The covariant representation of the classical lattice net on its global system. -/
noncomputable abbrev rep : CovariantNetRepresentation (act (Λ := Λ)) (Gl Λ) :=
  covariantRep (hN := isFaithful Λ Bool) act

/-- Translation moves the spin observable at `x` to the one at `a + x`. -/
lemma β_spin (a : Multiplicative Λ) (x : Λ) :
    ((rep (Λ := Λ)).β a).1 (spin Λ x) = spin Λ (Multiplicative.toAdd a + x) := by
  have h1 : ((rep (Λ := Λ)).β a).1 (spin Λ x)
      = ofLoc _ _ (a • ({x} : Finset Λ)) ((act (Λ := Λ)).τ a {x} (spinObs Λ {x} x)) :=
    βChan_apply_ofLoc (hN := isFaithful Λ Bool) act a {x} (spinObs Λ {x} x)
  have h2 : (act (Λ := Λ)).τ a {x} (spinObs Λ {x} x)
      = spinObs Λ (a • ({x} : Finset Λ)) (a • x) := by
    funext c
    change spinObs Λ {x} x (cfgEquiv Λ Bool (Multiplicative Λ) a {x} c)
      = spinObs Λ (a • ({x} : Finset Λ)) (a • x) c
    simp [spinObs, cfgEquiv]
    try rfl
  rw [h1, h2]
  exact ofLoc_spinObs _ (Finset.smul_mem_smul_finset (Finset.mem_singleton_self x))

/-- The linear map from coefficients to observables intertwines translations. -/
lemma spinMap_translation (a : Multiplicative Λ) (ψ : Λ →₀ ℝ) :
    spinMap (Crystal.translation (K := ℝ) a ψ) = (rep (Λ := Λ)).linearAction a (spinMap ψ) := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x m =>
    rw [Crystal.translation_single, spinMap_single, spinMap_single, map_smul,
      CovariantNetRepresentation.linearAction_apply, β_spin, add_comm]

/-!

## D. The unit-cell structure

-/

/-- The spin-wave sector: the span of the spin observables. -/
noncomputable abbrev sector : Submodule ℝ (Gl Λ) := LinearMap.range spinMap

lemma linearAction_mem (a : Multiplicative Λ) {w : Gl Λ} (hw : w ∈ sector (Λ := Λ)) :
    (rep (Λ := Λ)).linearAction a w ∈ sector (Λ := Λ) := by
  obtain ⟨ψ, rfl⟩ := hw
  exact ⟨Crystal.translation (K := ℝ) a ψ, spinMap_translation a ψ⟩

/-- Translation acting on the spin-wave sector. -/
noncomputable def actionW : Multiplicative Λ →* Module.End ℝ (sector (Λ := Λ)) where
  toFun a := ((rep (Λ := Λ)).linearAction a).restrict fun _ hw => linearAction_mem a hw
  map_one' := LinearMap.ext fun w => Subtype.ext (by simp)
  map_mul' a b := LinearMap.ext fun w => Subtype.ext (by simp [map_mul])

/-- **The spin-wave sector has a unit-cell structure**: it is `Λ →₀ ℝ`, one real mode per cell,
with translation acting by translation of configurations. -/
noncomputable def unitCell : UnitCellStructure (actionW (Λ := Λ)) ℝ where
  Φ := LinearEquiv.ofInjective spinMap spinMap_injective
  Φ_translation a ψ := Subtype.ext (spinMap_translation a ψ)

/-- **Bloch Hamiltonian of the spin-wave sector.** Hopping dynamics with hopping coefficients `H`
has Bloch matrix `∑ n, χ n • H n` at the character `χ`. -/
lemma bloch_hopping (χ : AddChar Λ ℝ) (H : Λ →₀ (ℝ →ₗ[ℝ] ℝ)) :
    blochMatrix (unitCell (Λ := Λ)) χ ((unitCell (Λ := Λ)).hopping H)
      = H.sum fun n Hn => χ n • Hn :=
  blochMatrix_hopping _ χ H

/-- **Bloch Hamiltonian at complex momenta.** On the complexified spin-wave sector, hopping
dynamics with complex hopping coefficients `H` has Bloch matrix `∑ n, χ n • H n` at every complex
character `χ`. -/
lemma bloch_hopping_complex (χ : AddChar Λ ℂ) (H : Λ →₀ (ℂ →ₗ[ℂ] ℂ)) :
    blochMatrix ((unitCell (Λ := Λ)).complexify) χ ((unitCell (Λ := Λ)).complexify.hopping H)
      = H.sum fun n Hn => χ n • Hn :=
  blochMatrix_hopping _ χ H

/-- A global channel commuting with translation and preserving the spin-wave sector restricts to
an equivariant map of the sector. -/
lemma isEquivariant_restrict {D : Channel (Gl Λ) (Gl Λ)} (hD : (rep (Λ := Λ)).Commutes D)
    (hW : ∀ w ∈ sector (Λ := Λ), D w ∈ sector (Λ := Λ)) :
    Crystal.IsEquivariant (actionW (Λ := Λ)) (actionW (Λ := Λ)) (D.toLinearMap.restrict hW) :=
  fun a w => Subtype.ext (hD a w)

/-- **Bloch relation for real dynamics.** A real channel of the global system commuting with
translation and preserving the spin-wave sector acts, after complexification, on Fourier
evaluations at every complex character through its Bloch matrix. -/
lemma bloch_relation_complex {D : Channel (Gl Λ) (Gl Λ)} (hD : (rep (Λ := Λ)).Commutes D)
    (hW : ∀ w ∈ sector (Λ := Λ), D w ∈ sector (Λ := Λ)) (χ : AddChar Λ ℂ)
    (v : ℂ ⊗[ℝ] (sector (Λ := Λ))) :
    Crystal.ev χ ((unitCell (Λ := Λ)).complexify.Φ.symm
        (((D.toLinearMap.restrict hW).baseChange ℂ) v))
      = blochMatrix ((unitCell (Λ := Λ)).complexify) χ ((D.toLinearMap.restrict hW).baseChange ℂ)
          (Crystal.ev χ ((unitCell (Λ := Λ)).complexify.Φ.symm v)) :=
  (unitCell (Λ := Λ)).complexify.ev_symm_apply
    (isEquivariant_baseChange (isEquivariant_restrict hD hW)) χ v

/-- **Nearest-neighbour chain.** On the integer lattice, hopping to the two neighbours with
amplitude `1` has Bloch matrix `χ 1 + χ (-1)`, which is `2 cos k` at the character of momentum
`k`. -/
lemma bloch_nearest_neighbour (χ : AddChar ℤ ℂ) :
    blochMatrix ((unitCell (Λ := ℤ)).complexify) χ
        ((unitCell (Λ := ℤ)).complexify.hopping
          (Finsupp.single 1 LinearMap.id + Finsupp.single (-1) LinearMap.id))
      = (χ 1 + χ (-1)) • LinearMap.id := by
  rw [bloch_hopping_complex, Finsupp.sum_add_index' (by simp) (by simp),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), add_smul]

end SpinWaves

end SpinLattice

end CondensedMatter
