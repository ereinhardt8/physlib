/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.GlobalSymmetry
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Lattice
public import PhyslibAlpha.ProbabilisticTheory.Classical.FiniteSystem

/-!

# Classical spins on a lattice

The local observables of a lattice of two-state spins, and their translation symmetry.

## i. Overview

Place a classical two-state spin, up or down, on every site of a lattice `S`. The observables
that can be measured inside a finite set of sites `X` are the real functions of the spins in `X`:
the magnetization of a block, the product of two neighbouring spins, the energy of a bond. They are
ordered pointwise, and the constant function `1` is the certain outcome. A function of the spins in
`X` is also a function of the spins in any larger region `Y`: this is the inclusion `X ≤ Y`. Moving
the sites by a symmetry of the lattice, for instance a translation, moves the observables along.

This is the kinematics on which the Ising model and its generalizations are defined: expectation
values of local observables in a state of the infinite lattice are the correlation functions of the
corresponding classical statistical mechanics. In this file:

* the net of local observables is built and shown to be faithful: a function of the spins in `X`
  is determined by its values as a function of the spins in a larger region, when a spin has
  a value at all;
* the translations act on it, so the net is covariant;
* the general theory then gives the observables of the infinite lattice, the translations acting on
  them, and the identification of homogeneous states of the infinite lattice with homogeneous
  families of local expectation values.

## ii. Key results

- `net` : the real functions of the spins in each finite region.
- `isFaithful` : a function of spins in a region stays distinguishable in a larger one.
- `netAction` : the lattice symmetries move the local observables.
- `isInvariant_stateEquiv_iff` : a state of the infinite lattice is homogeneous exactly when all
  its local expectation values are.

## iii. Table of contents

- A. Pullback of observables
- B. The net
- C. The group action

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.

-/

@[expose] public section

namespace CondensedMatter

namespace SpinLattice

open ProbabilisticTheory
open scoped Pointwise

variable (S σ : Type*) [DecidableEq S] [Fintype σ]

/-!

## A. Pullback of observables

-/

/-- Pulling back a classical observable along a map of outcome sets, as a channel. -/
def pullbackChan {α β : Type*} [Fintype α] [Fintype β] (φ : α → β) :
    Channel (FiniteClassicalSystem β) (FiniteClassicalSystem α) :=
  UnitalPositiveLinearMap.ofLinearMap (LinearMap.funLeft ℝ ℝ φ) (fun _ hf a => hf (φ a)) rfl

@[simp] lemma pullbackChan_apply {α β : Type*} [Fintype α] [Fintype β] (φ : α → β)
    (f : FiniteClassicalSystem β) (a : α) : pullbackChan φ f a = f (φ a) := rfl

/-- Pulling back along a composite is composing the pullbacks, in the opposite order. -/
lemma pullbackChan_comp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (φ : α → β)
    (ψ : β → γ) : (pullbackChan φ).comp (pullbackChan ψ) = pullbackChan (ψ ∘ φ) :=
  UnitalPositiveLinearMap.ext fun _ => rfl

/-- The classical observables of a finite region: real functions of its configurations. -/
abbrev Obs (X : Finset S) : Type _ := FiniteClassicalSystem (↥X → σ)

/-- Restriction of configurations from a region to a subregion. -/
def res {X Y : Finset S} (h : X ≤ Y) (c : ↥Y → σ) : ↥X → σ := fun x => c ⟨x.1, h x.2⟩

/-!

## B. The net

-/

/-- The net of local classical observables. -/
def net : LocalNet (Finset S) (Obs S σ) where
  incl h := pullbackChan (res S σ h)
  incl_refl _ := UnitalPositiveLinearMap.ext fun _ => rfl
  incl_trans _ _ := UnitalPositiveLinearMap.ext fun _ => rfl

/-- Every inclusion of the classical net is an order embedding, when there is a local state. -/
lemma isFaithful [Inhabited σ] : (net S σ).IsFaithful := by
  intro X Y h
  rw [Channel.isOrderEmbedding_iff_nonneg]
  intro f hf c
  let ext : ↥Y → σ := fun y => if hy : y.1 ∈ X then c ⟨y.1, hy⟩ else default
  have hres : res S σ h ext = c := by
    funext x
    simp [ext, res, x.2]
  have := hf ext
  simpa [net, hres] using this

/-!

## C. The group action

-/

variable (G : Type*) [Group G] [MulAction G S]

/-- Moving a configuration of `g • X` back to a configuration of `X`. -/
def cfgEquiv (g : G) (X : Finset S) : (↥(g • X) → σ) ≃ (↥X → σ) where
  toFun c x := c ⟨g • x.1, Finset.smul_mem_smul_finset x.2⟩
  invFun c y := c ⟨g⁻¹ • y.1, Finset.inv_smul_mem_iff.2 y.2⟩
  left_inv c := by
    funext y
    exact congrArg c (Subtype.ext (smul_inv_smul g y.1))
  right_inv c := by
    funext x
    exact congrArg c (Subtype.ext (inv_smul_smul g x.1))

/-- The local isomorphism of observables induced by moving configurations. -/
def τ (g : G) (X : Finset S) : OrderUnitIso (Obs S σ X) (Obs S σ (g • X)) where
  toChannel := pullbackChan (cfgEquiv S σ G g X)
  invChannel := pullbackChan (cfgEquiv S σ G g X).symm
  comp_inv := by
    rw [pullbackChan_comp]
    exact UnitalPositiveLinearMap.ext fun _ => by
      funext c; simp
  inv_comp := by
    rw [pullbackChan_comp]
    exact UnitalPositiveLinearMap.ext fun _ => by
      funext c; simp

lemma eqIso_apply {X Y : Finset S} (e : X = Y) (f : Obs S σ X) (c : ↥Y → σ) :
    eqIso (A := Obs S σ) e f c = f (fun x => c ⟨x.1, e ▸ x.2⟩) := by
  subst e; rfl

/-- The classical lattice net is covariant under the group action on sites. -/
def netAction : NetAction G (net S σ) where
  τ := τ S σ G
  τ_one X := OrderUnitIso.ext fun f => by
    funext c
    rw [eqIso_apply]
    exact congrArg f (funext fun x => congrArg c (Subtype.ext (one_smul G x.1)))
  τ_mul g h X := OrderUnitIso.ext fun f => by
    funext c
    simp only [OrderUnitIso.trans_apply, eqIso_apply]
    exact congrArg f (funext fun x => congrArg c (Subtype.ext (mul_smul g h x.1)))
  τ_incl g _ _ _ := UnitalPositiveLinearMap.ext fun _ => rfl

/-- **The headline theorem on the classical lattice net.** A state of the global system of
classical observables is invariant under the extended translations exactly when its family of
local states is invariant. -/
lemma isInvariant_stateEquiv_iff [Inhabited σ]
    (ω : 𝓢[ℝ, GlobalSystem (net S σ) (isFaithful S σ)]) :
    NetState.IsInvariant (netAction S σ G) (GlobalSystem.stateEquiv ω)
      ↔ ∀ g : G, ω.comp (GlobalSystem.globalβ (netAction S σ G) g).1 = ω :=
  GlobalSystem.isInvariant_stateEquiv_iff _ ω

end SpinLattice

end CondensedMatter
