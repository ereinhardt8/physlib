/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.SpinLattice.QuantumSpins
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Thermodynamic
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.ComplexExtension
public import Mathlib.Analysis.Complex.Basic

/-!

# Local thermal correlations in thermodynamic limits

Exact local analytic evolution lets finite-volume thermal boundary identities pass to every limit.

## i. Overview

A complex-time evolution that stabilizes inside a fixed finite neighborhood reduces thermal
correlations to expectations in that neighborhood. Convergence of local states therefore passes
the finite-volume KMS boundary identity to any thermodynamic limit state. The assumptions describe
the exact stabilization used by commuting interactions. No particular interaction or choice of
exhausting family enters the limit argument.

This is a local analytic boundary condition. A completed C*-algebra KMS theorem additionally needs
strip bounds and extension to the completed observables; neither is claimed here.

## ii. Key results

- `cplx`: complex-linear expectations of arbitrary local operators.
- `tendsto_cplx_of_isLimit`: operator expectations converge for any thermodynamic limit state.
- `LocalAnalyticEvolution`: finite-volume evolution with exact local analytic stabilization.
- `LocalAnalyticEvolution.IsLocalKMS`: the local analytic thermal boundary condition.
- `LocalAnalyticEvolution.isLocalKMS_of_isLimit`: thermal boundary identities pass to the limit.

## iii. Table of contents

- A. Operator expectations and convergence
- B. Exact local analytic evolution
- C. Thermal boundary identities in the limit

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.3.

-/

@[expose] public section

namespace CondensedMatter.SpinLattice.QuantumSpins

open ProbabilisticTheory ComplexStarModule
open scoped ComplexOrder Matrix Classical

variable {S : Type*} [DecidableEq S]

/-!

## A. Operator expectations and convergence

-/

/-- The expectation value of an arbitrary operator on the spins of a region in a state `φ`,
extending the expectation values of the observables linearly. -/
noncomputable def cplx {Y : Finset S} (φ : 𝓢[ℝ, QuantumSpins.Obs Y]) : Alg Y →ₗ[ℂ] ℂ :=
  (complexExtension φ.toLinearMap).comp (CStarMatrix.ofMatrixₗ (R := ℂ)).toLinearMap

lemma cplx_apply {Y : Finset S} (φ : 𝓢[ℝ, QuantumSpins.Obs Y]) (M : Alg Y) :
    cplx φ M = φ (ℜ (CStarMatrix.ofMatrix M)) + Complex.I * φ (ℑ (CStarMatrix.ofMatrix M)) :=
  rfl

/-- The real part of an operator is carried to the real part of its image by the inclusion of a
smaller region into a larger one. -/
lemma realPart_inclC {X Y : Finset S} (h : X ≤ Y) (a : CStarMatrix (Cfg X) (Cfg X) ℂ) :
    ℜ (inclC h a) = (QuantumSpins.net (S := S)).incl h (ℜ a) :=
  Subtype.ext (realPart_linearMap (inclC h).toAlgHom.toLinearMap (fun a => map_star (inclC h) a) a)

lemma imaginaryPart_inclC {X Y : Finset S} (h : X ≤ Y) (a : CStarMatrix (Cfg X) (Cfg X) ℂ) :
    ℑ (inclC h a) = (QuantumSpins.net (S := S)).incl h (ℑ a) :=
  Subtype.ext (imaginaryPart_linearMap (inclC h).toAlgHom.toLinearMap
    (fun a => map_star (inclC h) a) a)

/-- The expectation value of the operator `Q ⊗ 1` of a larger region is computed from the
expectation values of the local observables `ℜ Q` and `ℑ Q`. -/
lemma cplx_inclMat {X Y : Finset S} (h : X ≤ Y) (φ : 𝓢[ℝ, QuantumSpins.Obs Y]) (Q : Alg X) :
    cplx φ (inclMat h Q) =
      φ ((QuantumSpins.net (S := S)).incl h (ℜ (CStarMatrix.ofMatrix Q))) +
        Complex.I * φ ((QuantumSpins.net (S := S)).incl h (ℑ (CStarMatrix.ofMatrix Q))) := by
  rw [cplx_apply, ← realPart_inclC, ← imaginaryPart_inclC]
  rfl

/-- Convergence of local self-adjoint expectations gives convergence for arbitrary operators. -/
lemma tendsto_cplx_of_isLimit (F : ThermodynamicFamily (A := Obs (S := S)) (net (S := S)))
    {ω : NetState (net (S := S))} (hω : F.IsLimit ω) (X : Finset S) (Q : Alg X) :
    Filter.Tendsto
      (fun i => if h : X ≤ F.Λ i then cplx (F.ω i) (inclMat h Q) else 0)
      (F.U : Filter F.ι) (nhds (cplx (ω.ω X) Q)) := by
  have hR := hω X (ℜ (CStarMatrix.ofMatrix Q))
  have hI := hω X (ℑ (CStarMatrix.ofMatrix Q))
  have hlim := (Complex.continuous_ofReal.continuousAt.tendsto.comp hR).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hI).const_mul Complex.I)
  change Filter.Tendsto _ _ (nhds
    ((ω.ω X (ℜ (CStarMatrix.ofMatrix Q)) : ℂ) +
      Complex.I * (ω.ω X (ℑ (CStarMatrix.ofMatrix Q)) : ℂ)))
  apply hlim.congr'
  filter_upwards [F.eventually_le X] with i hi
  simp only [hi, ↓reduceDIte, Function.comp_apply]
  rw [F.val_of_le _ hi, F.val_of_le _ hi]
  exact (cplx_inclMat hi (F.ω i) Q).symm

/-!

## B. Exact local analytic evolution

-/

/-- Finite-volume complex-time evolution whose action on local operators stabilizes in a finite
region. Analyticity is a property of the evolution, independent of the equilibrium state. -/
structure LocalAnalyticEvolution (S : Type*) [DecidableEq S] where
  /-- A finite region supporting the complex-time evolution of an operator from `X`. -/
  support : Finset S → Finset S
  /-- The supporting region contains the original observable. -/
  le_support : ∀ X, X ≤ support X
  /-- Evolution of operators in a finite volume. -/
  evolve : ∀ Y : Finset S, ℂ → Alg Y → Alg Y
  /-- Time zero leaves the operator unchanged. -/
  evolve_zero : ∀ Y M, evolve Y 0 M = M
  /-- Complex-time evolutions compose by addition. -/
  evolve_add : ∀ Y s t M, evolve Y (s + t) M = evolve Y s (evolve Y t M)
  /-- Evolution of a local operator in its supporting region. -/
  evolveLocal : ∀ X : Finset S, ℂ → Alg X → Alg (support X)
  /-- Enlarging past the supporting region does not change the evolution. -/
  stabilizes : ∀ {X Y : Finset S} (h : support X ≤ Y) z N,
    inclMat h (evolveLocal X z N) = evolve Y z (inclMat ((le_support X).trans h) N)
  /-- Local correlations are entire for every linear expectation functional. -/
  analytic : ∀ X (L : Alg (support X) →ₗ[ℂ] ℂ) (P : Alg (support X)) (N : Alg X),
    Differentiable ℂ (fun z => L (P * evolveLocal X z N))

/-!

## C. Thermal boundary identities in the limit

-/

namespace LocalAnalyticEvolution

variable (D : LocalAnalyticEvolution S)

/-- The local analytic KMS boundary condition at inverse temperature `β`. -/
def IsLocalKMS (β : ℝ) (ω : NetState (net (S := S))) : Prop :=
  ∀ X (M N : Alg X), ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    (∀ t : ℝ, F t = cplx (ω.ω (D.support X))
      (inclMat (D.le_support X) M * D.evolveLocal X t N)) ∧
    ∀ t : ℝ, F (t + β * Complex.I) = cplx (ω.ω (D.support X))
      (D.evolveLocal X t N * inclMat (D.le_support X) M)

/-- Thermal boundary identities in finite volumes pass to every thermodynamic limit state,
provided the complex-time evolution has exact local stabilization. -/
lemma isLocalKMS_of_isLimit (β : ℝ) (F : ThermodynamicFamily (A := Obs (S := S)) (net (S := S)))
    {ω : NetState (net (S := S))} (hω : F.IsLimit ω)
    (hthermal : ∀ i (M N : Alg (F.Λ i)) (t : ℝ),
      cplx (F.ω i) (M * D.evolve (F.Λ i) (t + β * Complex.I) N) =
        cplx (F.ω i) (D.evolve (F.Λ i) t N * M)) : D.IsLocalKMS β ω := by
  intro X M N
  refine ⟨fun z => cplx (ω.ω (D.support X))
    (inclMat (D.le_support X) M * D.evolveLocal X z N),
    D.analytic X _ _ N, fun _ => rfl, ?_⟩
  intro t
  have h1 := tendsto_cplx_of_isLimit F hω (D.support X)
    (inclMat (D.le_support X) M * D.evolveLocal X (t + β * Complex.I) N)
  have h2 := tendsto_cplx_of_isLimit F hω (D.support X)
    (D.evolveLocal X t N * inclMat (D.le_support X) M)
  apply tendsto_nhds_unique_of_eventuallyEq h1 h2
  filter_upwards [F.eventually_le (D.support X)] with i hi
  simp only [hi, ↓reduceDIte, inclMat_mul, D.stabilizes, ← inclMat_trans]
  exact hthermal i _ _ t

end LocalAnalyticEvolution

end CondensedMatter.SpinLattice.QuantumSpins
