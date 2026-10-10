/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.IsingModel.ClassicalGibbs
public import PhyslibAlpha.CondensedMatter.SpinLattice.QuantumSpins
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Thermodynamic

/-!

# Equilibrium states of the Ising model

The Gibbs states of the classical and of the quantum Ising model in a finite region, and the states
of the infinite lattice that arise from them in the thermodynamic limit.

## i. Overview

A finite region `Y` of an Ising system in thermal equilibrium at inverse temperature `β` is in the
*Gibbs state*, in which the configuration `c` of its spins has probability
`exp (- β E_Y(c)) / Z_Y`. The expectation value of an observable depends on the model:

* in the classical Ising model an observable is a function `f` of the configuration and its
  expectation value is `∑ c, f c exp (- β E_Y(c)) / Z_Y`;
* in the quantum Ising model an observable is a self-adjoint operator `M` on the spins, the
  Hamiltonian is diagonal in the `σᶻ` basis with the eigenvalue `E_Y(c)` on `c`, and the expectation
  value is `tr (exp (- β H_Y) M) / Z_Y = ∑ c, M (c, c) exp (- β E_Y(c)) / Z_Y`.

For a function `f` on configurations, which is a diagonal operator, the two expectation values
agree: the classical model is the `σᶻ` sector of the quantum model.

The finite-volume Gibbs states are generally not compatible under restriction: boundary
interactions change when the region grows. They nevertheless define a *thermodynamic limit*
along a chosen ultrafilter containing the tails of the finite regions. Compactness gives limits
of local expectations, and those limits are compatible, hence define a state of the net.
This construction proves existence of a limit point. It does not prove uniqueness, convergence
along all finite regions, translation invariance, or the occurrence of a phase transition.

## ii. Key results

- `IsingModel.gibbsClassical` : the Gibbs state of the classical Ising model in a region.
- `IsingModel.gibbs` : the Gibbs state of the quantum Ising model in a region.
- `IsingModel.thermodynamicFamily` : the Gibbs states of the finite regions, exhausting the
  lattice.
- `IsingModel.thermodynamicLimitClassical` : a limit of classical Gibbs states.
- `IsingModel.tendsto_thermodynamicLimitClassical` : convergence of local classical expectations
  along the chosen ultrafilter.
- `IsingModel.thermodynamicLimit` : the corresponding construction for quantum spins.

## iii. Table of contents

- A. Gibbs states of the quantum Ising model
- B. Thermodynamic limits

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd ed.,
  Section 6.2.
* L. D. Landau & E. M. Lifshitz, Statistical Physics, Part 1, Chapter 14. [ref: landau_statphys1]
-/

@[expose] public section

namespace CondensedMatter

namespace IsingModel

open ProbabilisticTheory SpinLattice QuantumSpins
open scoped ComplexOrder

variable {S : Type*} [DecidableEq S] (I : IsingModel S) (β : ℝ)

/-!

## A. Gibbs states of the quantum Ising model

-/

/-- The Gibbs state `tr (exp (- β H) M) / Z` of the quantum Ising model in a region: the expectation
value of a self-adjoint operator on the spins. The Hamiltonian is diagonal in the `σᶻ` basis. -/
noncomputable def gibbs (Y : Finset S) : 𝓢[ℝ, QuantumSpins.Obs Y] :=
  UnitalPositiveLinearMap.ofLinearMap
    { toFun := fun M => ∑ c : Cfg Y, I.prob β Y c * ((M : CStarMatrix (Cfg Y) (Cfg Y) ℂ) c c).re
      map_add' := fun M N => by
        change ∑ c : Cfg Y, I.prob β Y c *
            (((M : CStarMatrix (Cfg Y) (Cfg Y) ℂ) c c) +
              ((N : CStarMatrix (Cfg Y) (Cfg Y) ℂ) c c)).re = _
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r M => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        change I.prob β Y c * (((r : ℂ) • (M : CStarMatrix (Cfg Y) (Cfg Y) ℂ)) c c).re = _
        simp [mul_left_comm] }
    (fun M hM => Finset.sum_nonneg fun c _ => by
      refine mul_nonneg (I.prob_nonneg β Y c) ?_
      have h0 : (0 : CStarMatrix (Cfg Y) (Cfg Y) ℂ) ≤ (M : CStarMatrix (Cfg Y) (Cfg Y) ℂ) := hM
      have h1 := ((nonneg_iff_posSemidef _).1 h0).diag_nonneg (i := c)
      exact (Complex.nonneg_iff.1 h1).1)
    (by
      change ∑ c : Cfg Y, I.prob β Y c * ((1 : CStarMatrix (Cfg Y) (Cfg Y) ℂ) c c).re = 1
      simpa [CStarMatrix.one_apply_eq] using I.sum_prob β Y)

lemma gibbs_apply (Y : Finset S) (M : QuantumSpins.Obs Y) :
    I.gibbs β Y M = ∑ c : Cfg Y, I.prob β Y c * ((M : CStarMatrix (Cfg Y) (Cfg Y) ℂ) c c).re :=
  rfl

/-!

## B. Thermodynamic limits

-/

/-- The Gibbs states of the finite regions of the lattice, exhausting the lattice along an
ultrafilter on the finite regions. -/
noncomputable def thermodynamicFamily :
    ThermodynamicFamily (R := Finset S) (A := QuantumSpins.Obs) (QuantumSpins.net (S := S)) where
  ι := Finset S
  Λ := id
  ω Y := I.gibbs β Y
  U := Ultrafilter.of Filter.atTop
  eventually_le X := (Ultrafilter.of_le _) (Filter.eventually_ge_atTop X)

/-- A thermodynamic limit of the Gibbs states of the quantum Ising model: a state of the infinite
lattice. -/
noncomputable def thermodynamicLimit : NetState (QuantumSpins.net (S := S)) :=
  (I.thermodynamicFamily β).limitState

/-- **Thermodynamic limit.** The expectation values of every local observable of the quantum
Ising model in the Gibbs states of larger and larger regions converge to the expectation values in
a state of the infinite lattice. -/
lemma tendsto_thermodynamicLimit (X : Finset S) (M : QuantumSpins.Obs X) :
    Filter.Tendsto ((I.thermodynamicFamily β).val X M)
      ((I.thermodynamicFamily β).U : Filter (I.thermodynamicFamily β).ι)
      (nhds ((I.thermodynamicLimit β).ω X M)) :=
  (I.thermodynamicFamily β).tendsto_limitState X M

end IsingModel

end CondensedMatter
