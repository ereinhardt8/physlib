/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.SpinLattice.ClassicalSpins
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!

# Independent spins as a state of a local net

Products of one-site probabilities give compatible local expectations and a global state.

## i. Overview

Independent spins have the same one-site probability at every site. The probability of a
configuration in a finite region is the product of its one-site probabilities. Summing over
unobserved sites leaves the original distribution on the observed region, so these finite-volume
states already form a state of the net. This construction applies to any finite spin space.

## ii. Key results

- `productProb`: the probability of a local configuration.
- `productState`: expectation values in a finite region.
- `productState_restrict`: taking a marginal preserves the product distribution.
- `productNetState`: the compatible state of the infinite lattice.
- `productGlobalState`: the corresponding state of the algebraic global system.

## iii. Table of contents

- A. Finite-volume probabilities
- B. Marginals and global states
- C. Homogeneity

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Chapter 2.

-/

@[expose] public section

namespace CondensedMatter.SpinLattice

open ProbabilisticTheory
open scoped Classical Pointwise

variable {S σ : Type*} [DecidableEq S] [Fintype σ] [DecidableEq σ]
  (p : σ → ℝ) (hp : p ∈ stdSimplexSet σ)

/-!

## A. Finite-volume probabilities

-/

/-- The probability of a configuration of independent, identically distributed spins. -/
noncomputable def productProb (X : Finset S) (c : ↥X → σ) : ℝ := ∏ x, p (c x)

omit [DecidableEq S] [DecidableEq σ] in
include hp in
lemma productProb_nonneg (X : Finset S) (c : ↥X → σ) : 0 ≤ productProb p X c :=
  Finset.prod_nonneg fun x _ => hp.1 (c x)

omit [DecidableEq σ] in
include hp in
lemma sum_productProb (X : Finset S) : ∑ c : ↥X → σ, productProb p X c = 1 := by
  simp only [productProb]
  rw [← Fintype.prod_sum (fun (_ : ↥X) (b : σ) => p b)]
  simp [hp.2]

/-- The finite-volume state of independent spins with one-site probabilities `p`. -/
noncomputable def productState (X : Finset S) : 𝓢[ℝ, Obs S σ X] :=
  FiniteClassicalSystem.ofProbs (productProb p X)
    ⟨productProb_nonneg p hp X, sum_productProb p hp X⟩

lemma productState_apply (X : Finset S) (f : Obs S σ X) :
    productState p hp X f = ∑ c : ↥X → σ, productProb p X c * f c :=
  FiniteClassicalSystem.ofProbs_apply _ _ _

/-!

## B. Marginals and global states

-/

omit [Fintype σ] in
/-- The indicator of a local configuration factors into constraints on individual sites. -/
lemma configuration_indicator {X Y : Finset S} (h : X ≤ Y) (c : ↥X → σ) (d : ↥Y → σ) :
    (if res S σ h d = c then (1 : ℝ) else 0) =
      ∏ y : ↥Y, if hy : y.1 ∈ X then (if d y = c ⟨y.1, hy⟩ then 1 else 0) else 1 := by
  have he : res S σ h d = c ↔ ∀ y : ↥Y, ∀ hy : y.1 ∈ X, d y = c ⟨y.1, hy⟩ := by
    constructor
    · intro e y hy
      exact congrFun e ⟨y.1, hy⟩
    · intro e
      exact funext fun x => e ⟨x.1, h x.2⟩ x.2
  classical
  simp only [he]
  have hi : ∀ y : ↥Y,
      (if hy : y.1 ∈ X then (if d y = c ⟨y.1, hy⟩ then (1 : ℝ) else 0) else 1) =
        if ∀ hy : y.1 ∈ X, d y = c ⟨y.1, hy⟩ then 1 else 0 := by
    intro y
    by_cases hy : y.1 ∈ X <;> simp [hy]
  simp_rw [hi]
  rw [Fintype.prod_boole]

include hp in
/-- Summing over spins outside a region gives its original configuration probability. -/
lemma productProb_marginal {X Y : Finset S} (h : X ≤ Y) (c : ↥X → σ) :
    ∑ d : ↥Y → σ, productProb p Y d * (if res S σ h d = c then 1 else 0) =
      productProb p X c := by
  simp_rw [configuration_indicator h c, productProb, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (y : ↥Y) (b : σ) =>
    p b * (if hy : y.1 ∈ X then (if b = c ⟨y.1, hy⟩ then 1 else 0) else 1))]
  have hs : ∀ y : ↥Y,
      (∑ b : σ, p b * (if hy : y.1 ∈ X then (if b = c ⟨y.1, hy⟩ then 1 else 0) else 1)) =
        if hy : y.1 ∈ X then p (c ⟨y.1, hy⟩) else 1 := by
    intro y
    by_cases hy : y.1 ∈ X <;> simp [hy, hp.2]
  simp_rw [hs]
  classical
  rw [Finset.prod_dite]
  simp only [Finset.prod_const_one, mul_one]
  exact Finset.prod_bij (fun y _ => ⟨y.1.1, (Finset.mem_filter.1 y.2).2⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ e => Subtype.ext (Subtype.ext (congrArg (fun x : ↥X => x.1) e)))
    (fun x _ => ⟨⟨⟨x.1, h x.2⟩, by simp [x.2]⟩, Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

/-- Marginals of independent spins are independent spins with the same one-site distribution. -/
lemma productState_restrict {X Y : Finset S} (h : X ≤ Y) :
    (net S σ).restrict h (productState p hp Y) = productState p hp X := by
  apply UnitalPositiveLinearMap.ext
  intro f
  have he : ∀ c : ↥X → σ,
      (net S σ).restrict h (productState p hp Y) (Pi.single c 1) =
        productState p hp X (Pi.single c 1) := by
    intro c
    simpa [LocalNet.restrict_apply, net, pullbackChan_apply, productState_apply, Pi.single_apply]
      using productProb_marginal p hp h c
  change ((net S σ).restrict h (productState p hp Y)).toLinearMap f =
    (productState p hp X).toLinearMap f
  rw [FiniteClassicalSystem.apply_eq_sum, FiniteClassicalSystem.apply_eq_sum]
  exact Finset.sum_congr rfl fun c _ => congrArg (f c * ·) (he c)

/-- Independent spins as a compatible state of the whole lattice net. -/
noncomputable def productNetState : NetState (net S σ) where
  ω := productState p hp
  compat := productState_restrict p hp

/-- The independent-spin state on the algebraic global observable system. -/
noncomputable def productGlobalState [Inhabited σ] :
    𝓢[ℝ, GlobalSystem (net S σ) (isFaithful S σ)] :=
  GlobalSystem.stateEquiv.symm (productNetState p hp)

/-!

## C. Homogeneity

-/

variable {G : Type*} [Group G] [MulAction G S]

omit [Fintype σ] [DecidableEq σ] in
/-- Identical one-site probabilities are unchanged by moving the sites. -/
lemma productProb_translate (g : G) (X : Finset S) (c : ↥(g • X) → σ) :
    productProb p X (cfgEquiv S σ G g X c) = productProb p (g • X) c := by
  unfold productProb
  exact Finset.prod_bij
    (fun x _ => (⟨g • x.1, Finset.smul_mem_smul_finset x.2⟩ : ↥(g • X)))
    (fun _ _ => Finset.mem_univ _)
    (fun x _ y _ he => Subtype.ext (MulAction.injective g (congrArg Subtype.val he)))
    (fun y _ => ⟨⟨g⁻¹ • y.1, Finset.inv_smul_mem_iff.2 y.2⟩,
      Finset.mem_univ _, Subtype.ext (smul_inv_smul g y.1)⟩) (fun _ _ => rfl)

/-- The product net state is homogeneous under every symmetry moving the sites. -/
lemma productNetState_isInvariant :
    NetState.IsInvariant (netAction S σ G) (productNetState p hp) := by
  intro g X
  ext f
  change productState p hp (g • X) (τ S σ G g X f) = productState p hp X f
  simp only [productState_apply]
  apply Fintype.sum_equiv (cfgEquiv S σ G g X)
  intro c
  rw [← productProb_translate p g X c]
  rfl

end CondensedMatter.SpinLattice
