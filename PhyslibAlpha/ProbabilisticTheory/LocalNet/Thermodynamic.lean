/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Symmetry
public import PhyslibAlpha.ProbabilisticTheory.LocalNet.State
public import PhyslibAlpha.ProbabilisticTheory.State.StateSpace

/-!

# The thermodynamic limit

Limits of finite-volume expectations define compatible states of the infinite system.

## i. Overview

Macroscopic equilibrium is idealised as a state of the infinite system, obtained as a limit of
states of larger and larger finite boxes. That such limits exist is a compactness statement: the
set of states of each local system is compact, so along an ultrafilter of boxes exhausting the
system the expectation values of every local observable converge. The limits are automatically
compatible with enlargement of regions, because inclusions compose, so the limit is a state of the
net with no further assumption.

The finite-volume states need not be equilibrium states. The theorem constructs a limit along a
chosen exhausting ultrafilter; it does not assert convergence along the full family of volumes or
uniqueness of the thermodynamic limit.

Properties that survive the limit are inherited by it. In particular if the finite-volume states
become invariant under translations in the limit of large boxes, the limit is homogeneous. This is
the standard route to translation-invariant states of the infinite system, and it applies to
classical and quantum systems alike.

## ii. Key results

- `ThermodynamicFamily` : states of larger and larger boxes exhausting the system.
- `ThermodynamicFamily.exists_limit` : a state of the infinite system exists as a limit.
- `ThermodynamicFamily.limitState` : a chosen limit of the finite-volume states.
- `ThermodynamicFamily.isInvariant_limitState` : asymptotic homogeneity gives a homogeneous
  limit.

## iii. Table of contents

- A. Finite-volume expectations
- B. Existence of limit points
- C. Invariance of limit points

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd ed.,
  Chapter 5.

-/

@[expose] public section

namespace ProbabilisticTheory

open Filter Topology
open scoped Classical

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, ArchimedeanOrderUnitSpace (A X)]

/-!

## A. Finite-volume expectations

-/

/-- States on the local systems of volumes `Λ i` that exhaust the regions along an ultrafilter. -/
structure ThermodynamicFamily (N : LocalNet R A) where
  /-- The index type of volumes. -/
  ι : Type*
  /-- The region of each volume. -/
  Λ : ι → R
  /-- The finite-volume state. -/
  ω : ∀ i, 𝓢[ℝ, A (Λ i)]
  /-- The ultrafilter along which we take limits. -/
  U : Ultrafilter ι
  /-- Every region is eventually contained in the volumes. -/
  eventually_le : ∀ X : R, ∀ᶠ i in (U : Filter ι), X ≤ Λ i

namespace ThermodynamicFamily

variable {N : LocalNet R A} (F : ThermodynamicFamily N)

/-- The finite-volume expectation of a local observable of `X`, defined when `X ≤ Λ i` and set to
`0` otherwise. -/
noncomputable def val (X : R) (a : A X) (i : F.ι) : ℝ :=
  if h : X ≤ F.Λ i then F.ω i (N.incl h a) else 0

lemma val_of_le {X : R} (a : A X) {i : F.ι} (h : X ≤ F.Λ i) :
    F.val X a i = F.ω i (N.incl h a) := by
  simp [val, h]

/-!

## B. Existence of limit points

-/

/-- A thermodynamic limit state has the limiting expectation of every local observable. -/
def IsLimit (σ : NetState N) : Prop :=
  ∀ (X : R) (a : A X), Tendsto (F.val X a) (F.U : Filter F.ι) (𝓝 (σ.ω X a))

/-- The limit along a fixed exhausting ultrafilter is determined by its local expectations. -/
lemma IsLimit.unique {F : ThermodynamicFamily N} {σ τ : NetState N}
    (hσ : F.IsLimit σ) (hτ : F.IsLimit τ) : σ = τ := by
  apply NetState.ext
  funext X
  exact UnitalPositiveLinearMap.ext fun a => tendsto_nhds_unique (hσ X a) (hτ X a)

/-- Limits of finite-volume expectations exist, and they define a state of every local
system. -/
lemma exists_local_limit (X : R) :
    ∃ φ : 𝓢[ℝ, A X], ∀ a : A X, Tendsto (F.val X a) (F.U : Filter F.ι) (𝓝 (φ a)) := by
  obtain ⟨i₀, hi₀⟩ := (F.eventually_le X).exists
  let base : 𝓢[ℝ, A X] := N.restrict hi₀ (F.ω i₀)
  have : Nonempty (stateSpace (A X)) := ⟨StateSpace.ofState base⟩
  let f : F.ι → stateSpace (A X) := fun i =>
    StateSpace.ofState (if h : X ≤ F.Λ i then N.restrict h (F.ω i) else base)
  have hφ : Tendsto f (F.U : Filter F.ι) (𝓝 (F.U.map f).lim) :=
    (F.U.map f).le_nhds_lim
  refine ⟨StateSpace.toState (F.U.map f).lim, fun a => ?_⟩
  have h1 := (StateSpace.tendsto_iff_forall_apply_tendsto.1 hφ) a
  refine h1.congr' ?_
  filter_upwards [F.eventually_le X] with i hi
  simp [f, val, hi]

/-- Limits along the ultrafilter exist and are compatible: **limit points of finite-volume states
are states of the net.** -/
lemma exists_limit :
    ∃ σ : NetState N, ∀ (X : R) (a : A X),
      Tendsto (F.val X a) (F.U : Filter F.ι) (𝓝 (σ.ω X a)) := by
  choose φ hφ using F.exists_local_limit
  refine ⟨⟨φ, fun {X Y} h => ?_⟩, hφ⟩
  refine DFunLike.ext _ _ fun a => ?_
  have h1 := hφ Y (N.incl h a)
  have h2 := hφ X a
  refine tendsto_nhds_unique_of_eventuallyEq h1 h2 ?_
  filter_upwards [F.eventually_le Y] with i hi
  rw [F.val_of_le _ hi, F.val_of_le _ (h.trans hi), N.incl_trans_apply h hi]

/-- A chosen thermodynamic limit point. -/
noncomputable def limitState : NetState N := F.exists_limit.choose

lemma tendsto_limitState (X : R) (a : A X) :
    Tendsto (F.val X a) (F.U : Filter F.ι) (𝓝 (F.limitState.ω X a)) :=
  F.exists_limit.choose_spec X a

/-- The chosen limit state realizes all limiting local expectations. -/
lemma isLimit_limitState : F.IsLimit F.limitState := F.tendsto_limitState

/-- A finite-volume family obtained by restricting a compatible state has that state as its
thermodynamic limit. This applies in particular to independent-spin product states. -/
lemma limitState_eq_of_compatible (σ : NetState N) (hω : ∀ i, F.ω i = σ.ω (F.Λ i)) :
    F.limitState = σ := by
  apply F.isLimit_limitState.unique
  intro X a
  apply tendsto_const_nhds.congr'
  filter_upwards [F.eventually_le X] with i hi
  rw [F.val_of_le a hi, hω i, σ.compat_apply hi]

/-!

## C. Invariance of limit points

-/

variable {G : Type*} [Group G] [MulAction G R] [RegionAction G R] {α : NetAction G N}

/-- **Asymptotic invariance passes to the limit.** If the finite-volume expectations of an
observable and of its translate agree in the limit, the limit point is invariant. -/
lemma isInvariant_limitState
    (h : ∀ (g : G) (X : R) (a : A X),
      Tendsto (fun i => F.val (g • X) (α.τ g X a) i - F.val X a i) (F.U : Filter F.ι) (𝓝 0)) :
    NetState.IsInvariant α F.limitState := by
  intro g X
  refine DFunLike.ext _ _ fun a => ?_
  have h1 := (F.tendsto_limitState (g • X) (α.τ g X a)).sub (F.tendsto_limitState X a)
  have := tendsto_nhds_unique h1 (h g X a)
  simpa [sub_eq_zero] using this

end ThermodynamicFamily

end ProbabilisticTheory
