/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.IsingModel.Basic
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Thermodynamic

/-!

# Classical Ising Gibbs states and thermodynamic limits

Finite-volume Gibbs expectations have compatible limit points on the classical spin net.

## i. Overview

In a finite region the Gibbs probability is the Boltzmann weight divided by the partition
function. Summing a local observable against this probability defines a state. Enlarging the
region changes the boundary interactions, so these states need not agree under restriction.
The general thermodynamic-limit construction produces compatible local expectations along an
exhausting ultrafilter. This file uses only classical observables.

## ii. Key results

- `gibbsClassical`: finite-volume Gibbs expectations.
- `thermodynamicFamilyClassical`: an exhausting family of finite-volume states.
- `thermodynamicLimitClassical`: a compatible infinite-volume state.
- `tendsto_thermodynamicLimitClassical`: local expectations converge along the ultrafilter.

## iii. Table of contents

- A. Finite-volume probabilities and states
- B. Thermodynamic limit points

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.

-/

@[expose] public section

namespace CondensedMatter

namespace IsingModel

open ProbabilisticTheory SpinLattice

variable {S : Type*} [DecidableEq S] (I : IsingModel S) (β : ℝ)

/-!

## A. Finite-volume probabilities and states

-/

/-- The Gibbs probability of a configuration of the spins in `Y`. -/
noncomputable def prob (Y : Finset S) (c : (↥Y → Bool)) : ℝ := I.weight β Y c / I.partition β Y

lemma prob_nonneg (Y : Finset S) (c : (↥Y → Bool)) : 0 ≤ I.prob β Y c :=
  div_nonneg (I.weight_pos β Y c).le (I.partition_pos β Y).le

lemma sum_prob (Y : Finset S) : ∑ c : (↥Y → Bool), I.prob β Y c = 1 := by
  unfold prob
  rw [← Finset.sum_div]
  exact div_self (I.partition_pos β Y).ne'

/-- The Gibbs state of the classical Ising model in a region: the expectation value of a function
of the spin configuration. -/
noncomputable def gibbsClassical (Y : Finset S) : 𝓢[ℝ, SpinLattice.Obs S Bool Y] :=
  UnitalPositiveLinearMap.ofLinearMap
    { toFun := fun f => ∑ c : (↥Y → Bool), I.prob β Y c * f c
      map_add' := fun f g => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r f => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring }
    (fun f hf => Finset.sum_nonneg fun c _ => mul_nonneg (I.prob_nonneg β Y c) (hf c))
    (by simpa using I.sum_prob β Y)

lemma gibbsClassical_apply (Y : Finset S) (f : SpinLattice.Obs S Bool Y) :
    I.gibbsClassical β Y f = ∑ c : (↥Y → Bool), I.prob β Y c * f c := rfl

/-!

## B. Thermodynamic limit points

-/

/-- The Gibbs states of the classical Ising model in the finite regions of the lattice. -/
noncomputable def thermodynamicFamilyClassical :
    ThermodynamicFamily (R := Finset S) (A := SpinLattice.Obs S Bool) (SpinLattice.net S Bool) where
  ι := Finset S
  Λ := id
  ω Y := I.gibbsClassical β Y
  U := Ultrafilter.of Filter.atTop
  eventually_le X := (Ultrafilter.of_le _) (Filter.eventually_ge_atTop X)

/-- A thermodynamic limit of the Gibbs states of the classical Ising model: a state of the infinite
lattice. -/
noncomputable def thermodynamicLimitClassical : NetState (SpinLattice.net S Bool) :=
  (I.thermodynamicFamilyClassical β).limitState

lemma tendsto_thermodynamicLimitClassical (X : Finset S) (f : SpinLattice.Obs S Bool X) :
    Filter.Tendsto ((I.thermodynamicFamilyClassical β).val X f)
      ((I.thermodynamicFamilyClassical β).U : Filter (I.thermodynamicFamilyClassical β).ι)
      (nhds ((I.thermodynamicLimitClassical β).ω X f)) :=
  (I.thermodynamicFamilyClassical β).tendsto_limitState X f

end IsingModel

end CondensedMatter
