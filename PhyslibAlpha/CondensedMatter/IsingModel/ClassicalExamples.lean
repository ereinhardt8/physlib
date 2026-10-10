/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.IsingModel.ClassicalGibbs
public import PhyslibAlpha.CondensedMatter.SpinLattice.ProductStates

/-!

# Independent spins and the uniform Ising chain

Explicit classical models instantiate the spin net and its thermodynamic-limit construction.

## i. Overview

Independent spins in a uniform field have an explicit product Gibbs distribution. Their local
states are compatible before taking a limit. The uniform nearest-neighbor Ising chain has an
interaction across region boundaries; its Gibbs states instead give a compatible limit point by
the general compactness theorem. Both models use the same classical observable net.

## ii. Key results

- `independent`: spins in a uniform field with no pair interactions.
- `independent_gibbs`: the finite-volume Gibbs state is a product state.
- `independent_limit`: its thermodynamic limit is the explicit product net state.
- `chain`: the uniform nearest-neighbor model on the integer lattice.
- `chain_coupling_translate`: translation invariance of its interaction.
- `chainGlobalState`: its thermodynamic limit as a state of the global system.

## iii. Table of contents

- A. Independent spins
- B. The uniform Ising chain

## iv. References

* E. Ising, Beitrag zur Theorie des Ferromagnetismus.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.

-/

@[expose] public section

namespace CondensedMatter.IsingModel

open ProbabilisticTheory SpinLattice
open scoped Classical

/-!

## A. Independent spins

-/

/-- Independent spins with a uniform field `h` and no pair interactions. -/
def independent (S : Type*) (h : ℝ) : IsingModel S where
  J _ _ := 0
  J_symm _ _ := rfl
  h _ := h
  nbrs _ := ∅
  J_support _ _ hn := (hn rfl).elim

/-- The one-site Boltzmann weight in the uniform field. -/
noncomputable def siteWeight (β h : ℝ) (b : Bool) : ℝ := Real.exp (β * h * sgn b)

/-- The one-site partition function. -/
noncomputable def sitePartition (β h : ℝ) : ℝ := ∑ b : Bool, siteWeight β h b

lemma sitePartition_pos (β h : ℝ) : 0 < sitePartition β h :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) (Finset.univ_nonempty)

/-- The probability of one independent spin at inverse temperature `β`. -/
noncomputable def siteProb (β h : ℝ) (b : Bool) : ℝ :=
  siteWeight β h b / sitePartition β h

lemma siteProb_mem_simplex (β h : ℝ) : siteProb β h ∈ stdSimplexSet Bool := by
  refine ⟨fun b => div_nonneg (Real.exp_pos _).le (sitePartition_pos β h).le, ?_⟩
  simp only [siteProb, ← Finset.sum_div]
  exact div_self (sitePartition_pos β h).ne'

variable {S : Type*} [DecidableEq S]

/-- Without pair interactions the Boltzmann weight factors over sites. -/
lemma independent_weight (β h : ℝ) (Y : Finset S) (c : ↥Y → Bool) :
    (independent S h).weight β Y c = ∏ y, siteWeight β h (c y) := by
  simp only [weight, energy, energyOf, independent, zero_mul, Finset.sum_const_zero,
    mul_zero, zero_sub]
  have he : -β * -(∑ i ∈ Y, h * sgn (extend c i)) = ∑ y : ↥Y, β * h * sgn (c y) := by
    rw [neg_mul_neg, Finset.mul_sum]
    rw [← Finset.sum_attach Y]
    simp [extend, mul_assoc]
  rw [he, Real.exp_sum]
  rfl

/-- The partition function of independent spins is a product of one-site partition functions. -/
lemma independent_partition (β h : ℝ) (Y : Finset S) :
    (independent S h).partition β Y = ∏ _ : ↥Y, sitePartition β h := by
  simp only [partition, independent_weight]
  exact (Fintype.prod_sum (fun (_ : ↥Y) (b : Bool) => siteWeight β h b)).symm

/-- Finite-volume Gibbs probabilities are products of the one-site probabilities. -/
lemma independent_prob (β h : ℝ) (Y : Finset S) (c : ↥Y → Bool) :
    (independent S h).prob β Y c = productProb (siteProb β h) Y c := by
  simp only [prob, independent_weight, independent_partition, productProb, siteProb]
  exact (Finset.prod_div_distrib (fun y => siteWeight β h (c y))
    (fun _ => sitePartition β h)).symm

/-- The independent-spin Gibbs state is an instance of the general product-state construction. -/
lemma independent_gibbs (β h : ℝ) (Y : Finset S) :
    (independent S h).gibbsClassical β Y =
      productState (siteProb β h) (siteProb_mem_simplex β h) Y := by
  ext f
  simp only [gibbsClassical_apply, productState_apply, independent_prob]

/-- The thermodynamic limit is the explicit product state, by compatibility of finite marginals. -/
lemma independent_limit (β h : ℝ) :
    (independent S h).thermodynamicLimitClassical β =
      productNetState (S := S) (siteProb β h) (siteProb_mem_simplex β h) :=
  ThermodynamicFamily.limitState_eq_of_compatible _ _ (independent_gibbs β h)

/-!

## B. The uniform Ising chain

-/

/-- The uniform nearest-neighbor Ising chain with coupling `J` and field `h`. -/
def chain (J h : ℝ) : IsingModel ℤ where
  J i j := if j = i - 1 ∨ j = i + 1 then J else 0
  J_symm i j := by
    have he : (j = i - 1 ∨ j = i + 1) ↔ (i = j - 1 ∨ i = j + 1) := by omega
    simp only [he]
  h _ := h
  nbrs i := {i - 1, i + 1}
  J_support i j hn := by
    by_cases he : j = i - 1 ∨ j = i + 1
    · simpa using he
    · exact (hn (ite_eq_right he)).elim

/-- Translating both sites leaves the exchange coupling unchanged. -/
lemma chain_coupling_translate (J h : ℝ) (a i j : ℤ) :
    (chain J h).J (a + i) (a + j) = (chain J h).J i j := by
  have he : (a + j = a + i - 1 ∨ a + j = a + i + 1) ↔
      (j = i - 1 ∨ j = i + 1) := by omega
  simp only [chain, he]

/-- The pair interaction vanishes between sites that are not nearest neighbors. -/
lemma chain_coupling_eq_zero (J h : ℝ) {i j : ℤ} (hn : ¬(j = i - 1 ∨ j = i + 1)) :
    (chain J h).J i j = 0 := ite_eq_right hn

/-- The classical Ising chain's thermodynamic limit on the algebraic global observable system. -/
noncomputable def chainGlobalState (J h β : ℝ) :
    𝓢[ℝ, GlobalSystem (SpinLattice.net ℤ Bool) (SpinLattice.isFaithful ℤ Bool)] :=
  GlobalSystem.stateEquiv.symm ((chain J h).thermodynamicLimitClassical β)

/-- The global state reproduces the compatible thermodynamic-limit state on all local regions. -/
lemma chainGlobalState_local (J h β : ℝ) :
    GlobalSystem.stateEquiv (chainGlobalState J h β) =
      (chain J h).thermodynamicLimitClassical β :=
  GlobalSystem.stateEquiv.apply_symm_apply _

end CondensedMatter.IsingModel
