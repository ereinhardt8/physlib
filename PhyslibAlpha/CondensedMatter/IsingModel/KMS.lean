/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.IsingModel.ClassicalExamples
public import PhyslibAlpha.CondensedMatter.IsingModel.GibbsStates
public import PhyslibAlpha.CondensedMatter.SpinLattice.ThermalLimit
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!

# Thermal equilibrium and the KMS condition for the Ising model

Local analytic thermal boundary identities for every thermodynamic limit of Ising Gibbs states.

## i. Overview

The quantum Ising model has the Hamiltonian `H_Y`, which is the multiplication by the energy
`E_Y(c)` on the `σᶻ` configuration `c`. An operator `M` of the spins in `Y` evolves in the
Heisenberg picture by `M ↦ exp (i t H_Y) M exp (- i t H_Y)`, which in the matrix elements is
`(α_t M) (c, c') = exp (i t (E_Y(c) - E_Y(c'))) M (c, c')`. The formula makes sense for complex
times `z`, where it is an entire function.

In an infinite lattice there is no Hamiltonian but there is a time evolution of every local
operator: the energy difference `E_Y(c) - E_Y(c')` of two configurations that agree outside a
region `X` is determined by the spins in the neighborhood of `X`, so an operator of the spins in
`X` evolves into an operator of the spins in the neighborhood of `X`, whatever the size of the
system. This is the local form of the dynamics of the infinite lattice.

A state is in thermal equilibrium at inverse temperature `β` when it satisfies the *KMS condition*
of Kubo, Martin and Schwinger: for any two local operators `A` and `B` the correlation function
`F(t) = ⟨A α_t(B)⟩` extends to a function that is analytic in the strip `0 ≤ Im z ≤ β` and satisfies
`F(t + i β) = ⟨α_t(B) A⟩`. This is the form of the Gibbs state `exp (- β H) / Z` that makes sense in
infinite volume, where the Gibbs state itself does not exist. For finite-range interactions
among commuting spins the extension is an entire function. The predicate formalized here is the
local analytic boundary condition. Strip boundedness and passage to completed observables remain
separate requirements for a completed-algebra KMS theorem.

This file proves, first, that the Gibbs state of every finite region is a KMS state for its own
evolution, and second, that every limit of an exhausting family of these Gibbs states satisfies
the local analytic boundary condition. The limit argument is an instance of the general theorem
in `SpinLattice.ThermalLimit`; uniqueness and a completed-algebra KMS result are not asserted.

## ii. Key results

- `IsingModel.evolve` : the Heisenberg evolution of an operator by complex time in a region.
- `IsingModel.evolveLocal` : the evolution of a local operator into its neighborhood.
- `IsingModel.gibbs_kms` : the Gibbs state of a finite region satisfies the KMS condition.
- `IsingModel.IsKMS` : the KMS condition for a state of the infinite lattice.
- `IsingModel.isKMS_thermodynamicLimit` : thermodynamic limits of Gibbs states are KMS states.

## iii. Table of contents

- A. Expectation values of operators
- B. Time evolution
- C. The KMS condition in a finite region
- D. The local dynamics
- E. The KMS condition in infinite volume
- F. The uniform longitudinal Ising chain

## iv. References

* R. Kubo, Statistical-mechanical theory of irreversible processes I.
* P. C. Martin & J. Schwinger, Theory of many-particle systems I.
* R. Haag, N. M. Hugenholtz & M. Winnink, On the equilibrium states in quantum statistical
  mechanics.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd ed.,
  Section 5.3.
-/

@[expose] public section

namespace CondensedMatter

namespace IsingModel

open ProbabilisticTheory SpinLattice QuantumSpins ComplexStarModule
open scoped ComplexOrder Matrix

variable {S : Type*} [DecidableEq S] (I : IsingModel S) (β : ℝ)

/-!

## A. Expectation values of operators

-/

/-- The diagonal entries of the real part of an operator are the real parts of its diagonal
entries. -/
lemma realPart_apply_diag {n : Type*} [Fintype n] [DecidableEq n] (a : CStarMatrix n n ℂ) (c : n) :
    (((ℜ a : selfAdjoint (CStarMatrix n n ℂ)) : CStarMatrix n n ℂ) c c).re = (a c c).re := by
  rw [realPart_apply_coe]
  change ((2 : ℝ)⁻¹ • (a c c + star (a c c))).re = _
  simp [Complex.add_re]
  ring

lemma imaginaryPart_apply_diag {n : Type*} [Fintype n] [DecidableEq n] (a : CStarMatrix n n ℂ)
    (c : n) :
    (((ℑ a : selfAdjoint (CStarMatrix n n ℂ)) : CStarMatrix n n ℂ) c c).re = (a c c).im := by
  rw [imaginaryPart_apply_coe]
  change (-Complex.I • ((2 : ℝ)⁻¹ • (a c c - star (a c c)))).re = _
  simp only [RCLike.star_def, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    smul_eq_mul, neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.inv_re,
    Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.sub_re, Complex.conj_re,
    sub_self, mul_zero, Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, Complex.sub_im,
    Complex.conj_im, sub_neg_eq_add, zero_mul, Complex.I_im, Complex.mul_im, add_zero,
    one_mul, zero_sub, neg_neg]
  ring

/-- **The Gibbs state, extended to operators, is the trace against the Gibbs density.** -/
lemma cplx_gibbs (Y : Finset S) (M : Alg Y) :
    cplx (I.gibbs β Y) M = ∑ c : Cfg Y, (I.prob β Y c : ℂ) * M c c := by
  rw [cplx_apply, gibbs_apply, gibbs_apply]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [realPart_apply_diag, imaginaryPart_apply_diag]
  apply Complex.ext <;> simp

/-!

## B. Time evolution

-/

/-- The Heisenberg evolution of an operator on the spins of `Y` by the complex time `z`:
`exp (i z H_Y) M exp (- i z H_Y)`, with matrix elements
`exp (i z (E_Y(c) - E_Y(c'))) M (c, c')`. For real `z` it is the time evolution. -/
noncomputable def evolve (Y : Finset S) (z : ℂ) (M : Alg Y) : Alg Y :=
  Matrix.of fun c c' =>
    Complex.exp (Complex.I * z * ((I.energy Y c - I.energy Y c' : ℝ) : ℂ)) * M c c'

lemma evolve_apply (Y : Finset S) (z : ℂ) (M : Alg Y) (c c' : Cfg Y) :
    I.evolve Y z M c c' =
      Complex.exp (Complex.I * z * ((I.energy Y c - I.energy Y c' : ℝ) : ℂ)) * M c c' := rfl

/-- **Convergence of expectation values of operators.** In the thermodynamic limit the expectation
values of an operator of the spins of `X` in the Gibbs states of larger and larger regions
converge to its expectation value in the state of the infinite lattice. -/
lemma tendsto_cplx_thermodynamicLimit (X : Finset S) (Q : Alg X) :
    Filter.Tendsto
      (fun Y : Finset S => if h : X ≤ Y then cplx (I.gibbs β Y) (inclMat h Q) else 0)
      ((Ultrafilter.of Filter.atTop : Ultrafilter (Finset S)) : Filter (Finset S))
      (nhds (cplx ((I.thermodynamicLimit β).ω X) Q)) :=
  tendsto_cplx_of_isLimit (I.thermodynamicFamily β)
    (I.thermodynamicFamily β).isLimit_limitState X Q

/-!

## C. The KMS condition in a finite region

-/

/-- The exponent identity behind the KMS condition: shifting the time by `i β` multiplies the
matrix element between `c` and `c'` by the ratio of the Gibbs weights. -/
lemma weight_mul_exp_kms (e e' : ℝ) (t : ℝ) :
    (Real.exp (-β * e) : ℂ) * Complex.exp (Complex.I * (t + β * Complex.I) * ((e' - e : ℝ) : ℂ)) =
      (Real.exp (-β * e') : ℂ) * Complex.exp (Complex.I * t * ((e' - e : ℝ) : ℂ)) := by
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The Gibbs state of a finite region satisfies the KMS condition** for its own time
evolution: `⟨A α_{t + i β}(B)⟩ = ⟨α_t(B) A⟩`. -/
lemma gibbs_kms (Y : Finset S) (A B : Alg Y) (t : ℝ) :
    cplx (I.gibbs β Y) (A * I.evolve Y (t + β * Complex.I) B) =
      cplx (I.gibbs β Y) (I.evolve Y t B * A) := by
  rw [cplx_gibbs, cplx_gibbs]
  simp only [Matrix.mul_apply, evolve_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  have hZ : (I.partition β Y : ℂ) ≠ 0 := by exact_mod_cast (I.partition_pos β Y).ne'
  have key := weight_mul_exp_kms β (I.energy Y c) (I.energy Y c') t
  have e1 : (I.prob β Y c : ℂ) = (Real.exp (-β * I.energy Y c) : ℂ) / I.partition β Y := by
    simp [prob, weight]
  have e2 : (I.prob β Y c' : ℂ) = (Real.exp (-β * I.energy Y c') : ℂ) / I.partition β Y := by
    simp [prob, weight]
  rw [e1, e2]
  linear_combination (A c c' * B c' c / (I.partition β Y : ℂ)) * key

/-!

## D. The local dynamics

-/

/-- The time evolution of an operator on the spins of `X`: an operator on the spins of the
neighborhood of `X`. It does not depend on how large the system is. -/
noncomputable def evolveLocal (X : Finset S) (z : ℂ) (N : Alg X) : Alg (I.plus X) :=
  I.evolve (I.plus X) z (inclMat (I.subset_plus X) N)

/-- **Locality of the dynamics.** The evolution of an operator on the spins of `X` in any region
containing its neighborhood is the evolution computed in the neighborhood. -/
lemma inclMat_evolveLocal {X Y : Finset S} (hY : I.plus X ≤ Y) (z : ℂ) (N : Alg X) :
    inclMat hY (I.evolveLocal X z N) =
      I.evolve Y z (inclMat ((I.subset_plus X).trans hY) N) := by
  ext c c'
  rw [inclMat_apply, evolve_apply, inclMat_apply]
  by_cases h : Agree ((I.subset_plus X).trans hY) c c'
  · obtain ⟨h1, h2⟩ := (agree_trans_iff (I.subset_plus X) hY c c').1 h
    have hE := I.energy_sub_energy ((I.subset_plus X).trans hY) hY h
    simp only [h, h1, ↓reduceIte, evolveLocal, evolve_apply, inclMat_apply, h2, hE]
    rfl
  · by_cases h1 : Agree hY c c'
    · have h2 : ¬Agree (I.subset_plus X) (restr hY c) (restr hY c') :=
        fun h2 => h ((agree_trans_iff (I.subset_plus X) hY c c').2 ⟨h1, h2⟩)
      simp [h, h1, evolveLocal, evolve_apply, inclMat_apply, h2]
    · simp [h, h1]

/-!

## E. The KMS condition in infinite volume

-/

/-- A linear functional on the operators of a region is determined by its values on the matrix
units. -/
lemma linear_functional_eq_sum {Y : Finset S} (L : Alg Y →ₗ[ℂ] ℂ) (Q : Alg Y) :
    L Q = ∑ a, ∑ b, Q a b * L (Matrix.single a b 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Q]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : Matrix.single a b (Q a b) = Q a b • Matrix.single a b (1 : ℂ) := by
    ext i j; simp [Matrix.single_apply]
  rw [this, map_smul, smul_eq_mul]

/-- Correlation functions of local operators are entire functions of the complex time: they are
finite sums of exponentials. -/
lemma differentiable_apply_mul_evolve (Y : Finset S) (L : Alg Y →ₗ[ℂ] ℂ) (P N : Alg Y) :
    Differentiable ℂ fun z : ℂ => L (P * I.evolve Y z N) := by
  have h : (fun z : ℂ => L (P * I.evolve Y z N)) = fun z : ℂ =>
      ∑ a, ∑ b, (∑ c, P a c * (Complex.exp (Complex.I * z *
        ((I.energy Y c - I.energy Y b : ℝ) : ℂ)) * N c b)) * L (Matrix.single a b 1) := by
    funext z
    rw [linear_functional_eq_sum]
    simp [Matrix.mul_apply, evolve_apply]
  rw [h]
  fun_prop

lemma evolve_zero (Y : Finset S) (M : Alg Y) : I.evolve Y 0 M = M := by
  ext c c'; simp [evolve_apply]

lemma evolve_add (Y : Finset S) (s t : ℂ) (M : Alg Y) :
    I.evolve Y (s + t) M = I.evolve Y s (I.evolve Y t M) := by
  ext c c'
  simp only [evolve_apply]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The Ising complex-time evolution is an instance of exact local analytic evolution. -/
noncomputable def analyticEvolution : LocalAnalyticEvolution S where
  support := I.plus
  le_support := I.subset_plus
  evolve := I.evolve
  evolve_zero := I.evolve_zero
  evolve_add := I.evolve_add
  evolveLocal := I.evolveLocal
  stabilizes := I.inclMat_evolveLocal
  analytic X L P N := I.differentiable_apply_mul_evolve (I.plus X) L P
    (inclMat (I.subset_plus X) N)

/-- The local analytic KMS boundary condition at inverse temperature `β` for a state of the
infinite lattice: for any
two local operators `M` and `N`, the correlation function `⟨M α_t(N)⟩` is the restriction to the
real line of an entire function `F` with `F (t + i β) = ⟨α_t(N) M⟩`. -/
def IsKMS (ω : NetState (QuantumSpins.net (S := S))) : Prop :=
  I.analyticEvolution.IsLocalKMS β ω

/-- Every limit of an exhausting family of Ising Gibbs states satisfies the local analytic KMS
boundary condition, independently of how the limit was selected. -/
lemma isKMS_of_isLimit
    (F : ThermodynamicFamily (A := QuantumSpins.Obs (S := S)) (QuantumSpins.net (S := S)))
    (hgibbs : ∀ i, F.ω i = I.gibbs β (F.Λ i))
    {ω : NetState (QuantumSpins.net (S := S))} (hω : F.IsLimit ω) : I.IsKMS β ω := by
  apply I.analyticEvolution.isLocalKMS_of_isLimit β F hω
  intro i M N t
  rw [hgibbs i]
  exact I.gibbs_kms β (F.Λ i) M N t

/-- **Thermodynamic limits of Gibbs states are in thermal equilibrium.** Every state of the
infinite lattice that is a thermodynamic limit of the Gibbs states of the finite regions satisfies
the KMS condition at inverse temperature `β` for the local dynamics of the quantum Ising model.
This holds in every dimension, for any exchange couplings of finite range, any field and any
temperature, including at a phase transition where the limit state is not unique. -/
theorem isKMS_thermodynamicLimit : I.IsKMS β (I.thermodynamicLimit β) :=
  I.isKMS_of_isLimit β (I.thermodynamicFamily β) (fun _ => rfl)
    (I.thermodynamicFamily β).isLimit_limitState

/-!

## F. The uniform longitudinal Ising chain

-/

/-- The quantum longitudinal Ising chain is an instance of the general exact local thermal-limit
argument. Its observable net contains all spin operators, including off-diagonal ones. -/
lemma chain_isKMS (J h β : ℝ) : (chain J h).IsKMS β ((chain J h).thermodynamicLimit β) :=
  (chain J h).isKMS_thermodynamicLimit β

end IsingModel

end CondensedMatter
