/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Representation
public import PhyslibAlpha.ProbabilisticTheory.State.Convex

/-!

# States of an extended system

Expectation values of all local measurements, and their homogeneity under a symmetry.

## i. Overview

A state assigns an expectation value to every measurement. For an infinite system the
macroscopic states of interest, such as thermal equilibrium of a crystal, cannot be given by a
density matrix. They are described by the expectation values of all the *local* measurements. A
state of a local net is therefore a family `ω X`, one state for the observables of each region,
which is compatible with enlargement: the expectation value of a measurement made in `X` does not
depend on the larger region in which it is regarded as made. No global system is needed to define
this.

A state is *invariant* under a symmetry when moving a measurement does not change its expectation
value, `ω (g • X) ∘ τ g X = ω X`. For translations, this is homogeneity of the state. Invariance
of a state is a different property from covariance of the system and from invariance of the time
evolution.

## ii. Key results

- `NetState` : expectation values of all local measurements, compatible with enlargement.
- `NetState.mix` : statistical mixtures of states.
- `NetState.act` : moving a state by a symmetry.
- `NetRepresentation.stateOf` : a state of the big system gives expectation values for all local
  measurements.
- `CovariantNetRepresentation.isInvariant_stateOf` : a homogeneous state of the big system gives
  a homogeneous state of the net.

## iii. Table of contents

- A. Compatible families
- B. Symmetry
- C. States from representations

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]

/-!

## A. Compatible families

-/

/-- A state of a local net: a compatible family of local states. -/
@[ext]
structure NetState (N : LocalNet R A) where
  /-- The state on the local system of `X`. -/
  ω : ∀ X, 𝓢[ℝ, A X]
  /-- Restriction of the state on `Y` is the state on `X`. -/
  compat : ∀ {X Y : R} (h : X ≤ Y), N.restrict h (ω Y) = ω X

namespace NetState

variable {N : LocalNet R A} {X Y : R}

lemma compat_apply (σ : NetState N) (h : X ≤ Y) (a : A X) : σ.ω Y (N.incl h a) = σ.ω X a :=
  DFunLike.congr_fun (σ.compat h) a

/-- Convex combination of compatible families. -/
def mix (σ τ : NetState N) (t : unitInterval) : NetState N where
  ω X := UnitalPositiveLinearMap.mix (σ.ω X) (τ.ω X) t
  compat h := by
    ext a
    simp [σ.compat_apply, τ.compat_apply]

@[simp] lemma mix_apply (σ τ : NetState N) (t : unitInterval) (X : R) (a : A X) :
    (σ.mix τ t).ω X a = (t : ℝ) * σ.ω X a + (1 - (t : ℝ)) * τ.ω X a := rfl

/-!

## B. Symmetry

-/

section Symmetry

variable {G : Type*} [Group G] [MulAction G R] [RegionAction G R] {α : NetAction G N}

/-- The family is invariant when `ω (g • X) ∘ τ g X = ω X`. -/
def IsInvariant (α : NetAction G N) (σ : NetState N) : Prop :=
  ∀ (g : G) (X : R), (α.τ g X).pullback (σ.ω (g • X)) = σ.ω X

/-- The local state of `σ` at `g • X`, pulled back to `X` along `τ g X`. -/
def pull (α : NetAction G N) (g : G) (X : R) (σ : NetState N) : 𝓢[ℝ, A X] :=
  (α.τ g X).pullback (σ.ω (g • X))

lemma isInvariant_iff_pull {σ : NetState N} :
    IsInvariant α σ ↔ ∀ (g : G) (X : R), pull α g X σ = σ.ω X := Iff.rfl

/-- Pulling a local state back along a transport isomorphism returns the state at the other
index. -/
lemma pullback_eqIso (e : X = Y) (σ : NetState N) : (eqIso e).pullback (σ.ω Y) = σ.ω X := by
  subst e; rfl

lemma pull_one (X : R) (σ : NetState N) : pull α 1 X σ = σ.ω X := by
  unfold pull
  rw [α.τ_one]
  exact pullback_eqIso _ σ

lemma pull_mul (g h : G) (X : R) (σ : NetState N) :
    pull α (g * h) X σ = (α.τ h X).pullback (pull α g (h • X) σ) := by
  unfold pull
  rw [α.τ_mul, OrderUnitIso.pullback_trans, OrderUnitIso.pullback_trans,
    pullback_eqIso (mul_smul g h X).symm σ]

/-- A net action moves compatible families to compatible families:
`(g · σ) X = σ (g⁻¹ • X) ∘ τ g⁻¹ X`. -/
def act (α : NetAction G N) (g : G) (σ : NetState N) : NetState N where
  ω X := pull α g⁻¹ X σ
  compat {X Y} h := by
    rw [pull, α.restrict_pullback g⁻¹ h, σ.compat]
    rfl

@[simp] lemma act_ω (g : G) (σ : NetState N) (X : R) : (act α g σ).ω X = pull α g⁻¹ X σ := rfl

lemma act_apply (g : G) (σ : NetState N) (X : R) (a : A X) :
    (act α g σ).ω X a = σ.ω (g⁻¹ • X) (α.τ g⁻¹ X a) := rfl

lemma act_one (σ : NetState N) : act α 1 σ = σ :=
  NetState.ext (funext fun X => by rw [act_ω, inv_one, pull_one])

lemma act_mul (g h : G) (σ : NetState N) : act α (g * h) σ = act α g (act α h σ) :=
  NetState.ext (funext fun X => by
    rw [act_ω, mul_inv_rev, pull_mul]
    rfl)

/-- The action of a net action on compatible families of states. -/
abbrev mulAction (α : NetAction G N) : MulAction G (NetState N) where
  smul := act α
  one_smul := act_one
  mul_smul := act_mul

/-- A family is invariant exactly when the group fixes it. -/
lemma isInvariant_iff_forall_act_eq {σ : NetState N} :
    IsInvariant α σ ↔ ∀ g : G, act α g σ = σ := by
  refine ⟨fun hσ g => NetState.ext (funext fun X => hσ g⁻¹ X), fun hfix g X => ?_⟩
  have h : pull α g⁻¹⁻¹ X σ = σ.ω X := congrArg (fun τ' => τ'.ω X) (hfix g⁻¹)
  rwa [inv_inv] at h

/-- Invariant families are fixed by every group element. -/
lemma IsInvariant.act_eq {σ : NetState N} (hσ : IsInvariant α σ) (g : G) : act α g σ = σ :=
  isInvariant_iff_forall_act_eq.1 hσ g

end Symmetry

end NetState

/-!

## C. States from representations

-/

namespace NetRepresentation

variable {N : LocalNet R A} {B : Type*} [OrderUnitSpace B] (ρ : NetRepresentation N B)

/-- A state of the target induces a compatible family of local states. -/
def stateOf (ω : 𝓢[ℝ, B]) : NetState N where
  ω X := ω.comp (ρ.π X)
  compat {X Y} h := by
    ext a
    simp [ρ.π_incl_apply h]

@[simp] lemma stateOf_apply (ω : 𝓢[ℝ, B]) (X : R) (a : A X) :
    (ρ.stateOf ω).ω X a = ω (ρ.π X a) :=
  rfl

end NetRepresentation

namespace CovariantNetRepresentation

variable {G : Type*} [Group G] [MulAction G R] [RegionAction G R] {N : LocalNet R A}
  {α : NetAction G N} {B : Type*} [OrderUnitSpace B] (ρ : CovariantNetRepresentation α B)

/-- An invariant target state induces an invariant compatible family. -/
lemma isInvariant_stateOf {ω : 𝓢[ℝ, B]} (hω : ∀ g : G, ω.comp (ρ.β g).1 = ω) :
    NetState.IsInvariant α (ρ.stateOf ω) := by
  intro g X
  ext a
  have := DFunLike.congr_fun (hω g) (ρ.π X a)
  simpa [ρ.covariant_apply g X a] using this

end CovariantNetRepresentation

end ProbabilisticTheory
