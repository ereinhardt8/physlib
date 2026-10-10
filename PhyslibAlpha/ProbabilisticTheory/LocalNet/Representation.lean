/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Symmetry
public import Mathlib.LinearAlgebra.Span.Basic

/-!

# Representations: the whole system in one place

Realising all the local observables as observables of one big system, with the symmetry acting on
it.

## i. Overview

In practice the local observables of a crystal all act on one Hilbert space, the state space
of the whole crystal. A *representation* is exactly that structure: every local observable is
regarded as an observable of one big system `B`, so that enlarging the region does not change the
observable, `π Y ∘ ι = π X`. It is *faithful* when no two distinguishable local observables become
indistinguishable in `B`, and the images then give the familiar picture of an increasing family of
local observables inside a common space.

A representation is *covariant* when the translations of the crystal are realised by symmetries of
`B`: `β g ∘ π X = π (g • X) ∘ τ g X`. For quantum systems these symmetries are implemented by
unitary operators, `β g b = U g b (U g)⁻¹`. No Hilbert space is assumed here, because probabilistic
theories without one are covered as well.

## ii. Key results

- `NetRepresentation` : all local observables realised inside one big system.
- `NetRepresentation.map` : passing to another description of the big system.
- `LocalNet.comap`, `NetRepresentation.comap` : keeping only some of the regions.
- `NetRepresentation.IsFaithful.net` : a faithful representation shows the net is faithful.
- `NetRepresentation.ambient` : the local observables as subspaces of the big system.
- `CovariantNetRepresentation` : a representation in which the symmetry acts on the big system.
- `CovariantNetRepresentation.restrictSubgroup` : using only a subgroup of the symmetries.

## iii. Table of contents

- A. Representations
- B. Restriction and composition
- C. Ambient realization
- D. Covariant representations

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]

/-!

## A. Representations

-/

/-- A representation of a local net in an order-unit space `B`. -/
structure NetRepresentation (N : LocalNet R A) (B : Type*) [OrderUnitSpace B] where
  /-- The channel from the local system of `X` into `B`. -/
  π : ∀ X, Channel (A X) B
  /-- Compatibility with inclusion. -/
  π_incl : ∀ {X Y : R} (h : X ≤ Y), (π Y).comp (N.incl h) = π X

namespace NetRepresentation

variable {N : LocalNet R A} {B B' : Type*} [OrderUnitSpace B] [OrderUnitSpace B']
  (ρ : NetRepresentation N B) {X Y : R}

lemma π_incl_apply (h : X ≤ Y) (a : A X) : ρ.π Y (N.incl h a) = ρ.π X a :=
  DFunLike.congr_fun (ρ.π_incl h) a

/-- A representation is faithful when each local map is an order embedding. -/
def IsFaithful : Prop := ∀ X, Channel.IsOrderEmbedding (ρ.π X)

/-- A faithful representation forces the net itself to be faithful. -/
lemma IsFaithful.net {ρ : NetRepresentation N B} (hρ : ρ.IsFaithful) : N.IsFaithful :=
  fun {X Y} h a b hab =>
    hρ X a b (by
      rw [← ρ.π_incl_apply h, ← ρ.π_incl_apply h]
      exact OrderHomClass.mono _ hab)

/-!

## B. Restriction and composition

-/

/-- Compose a representation with a channel of target systems. -/
def map (φ : Channel B B') : NetRepresentation N B' where
  π X := φ.comp (ρ.π X)
  π_incl h := by rw [← UnitalPositiveLinearMap.comp_assoc, ρ.π_incl h]

@[simp] lemma map_π (φ : Channel B B') (X : R) : (ρ.map φ).π X = φ.comp (ρ.π X) := rfl

lemma IsFaithful.map {ρ : NetRepresentation N B} (hρ : ρ.IsFaithful) {φ : Channel B B'}
    (hφ : Channel.IsOrderEmbedding φ) : (ρ.map φ).IsFaithful :=
  fun X => hφ.comp (hρ X)

/-- Composing with an isomorphism of targets keeps faithfulness. -/
lemma IsFaithful.mapIso {ρ : NetRepresentation N B} (hρ : ρ.IsFaithful) (e : OrderUnitIso B B') :
    (ρ.map e.toChannel).IsFaithful := hρ.map e.isOrderEmbedding

/-!

## C. Ambient realization

-/

/-- The ambient image of the local system of `X` inside `B`. -/
def ambient (X : R) : Submodule ℝ B := LinearMap.range (ρ.π X).toLinearMap

lemma mem_ambient {X : R} {b : B} : b ∈ ρ.ambient X ↔ ∃ a : A X, ρ.π X a = b := Iff.rfl

lemma π_mem_ambient (X : R) (a : A X) : ρ.π X a ∈ ρ.ambient X := ⟨a, rfl⟩

/-- Ambient images increase with the region. -/
lemma ambient_mono (h : X ≤ Y) : ρ.ambient X ≤ ρ.ambient Y := by
  rintro _ ⟨a, rfl⟩
  exact ⟨N.incl h a, ρ.π_incl_apply h a⟩

/-- The unit of `B` lies in every ambient image. -/
lemma one_mem_ambient (X : R) : (1 : B) ∈ ρ.ambient X := ⟨1, map_one (ρ.π X)⟩

/-- For a faithful representation, the local system is linearly isomorphic to its ambient
image. -/
noncomputable def ambientEquiv (hρ : ρ.IsFaithful) (X : R) : A X ≃ₗ[ℝ] ρ.ambient X :=
  LinearEquiv.ofInjective (ρ.π X).toLinearMap (hρ X).injective

/-!

## D. Covariant representations

-/

end NetRepresentation

/-- Pulling a net back along a monotone map of region posets. -/
def LocalNet.comap {R' : Type*} [PartialOrder R'] (N : LocalNet R A) (f : R' →o R) :
    LocalNet R' (fun X => A (f X)) where
  incl h := N.incl (f.monotone h)
  incl_refl X := N.incl_refl (f X)
  incl_trans h₁ h₂ := N.incl_trans (f.monotone h₁) (f.monotone h₂)

/-- Restricting a representation to a smaller family of regions. -/
def NetRepresentation.comap {N : LocalNet R A} {B : Type*} [OrderUnitSpace B]
    (ρ : NetRepresentation N B) {R' : Type*} [PartialOrder R'] (f : R' →o R) :
    NetRepresentation (N.comap f) B where
  π X := ρ.π (f X)
  π_incl h := ρ.π_incl (f.monotone h)

/-- A covariant representation of a net with a `G`-action: a representation together with a
homomorphism of `G` into the symmetries of the target, intertwining the local isomorphisms. -/
structure CovariantNetRepresentation {G : Type*} [Group G] [MulAction G R] [RegionAction G R]
    {N : LocalNet R A} (α : NetAction G N) (B : Type*) [OrderUnitSpace B]
    extends NetRepresentation N B where
  /-- The symmetry of the target. -/
  β : G →* Symmetry B
  /-- Covariance: `β g ∘ π X = π (g • X) ∘ τ g X`. -/
  covariant : ∀ (g : G) (X : R),
    (β g).1.comp (π X) = (π (g • X)).comp (α.τ g X).toChannel

namespace CovariantNetRepresentation

variable {G : Type*} [Group G] [MulAction G R] [RegionAction G R] {N : LocalNet R A}
  {α : NetAction G N} {B : Type*} [OrderUnitSpace B] (ρ : CovariantNetRepresentation α B)

lemma covariant_apply (g : G) (X : R) (a : A X) :
    (ρ.β g).1 (ρ.π X a) = ρ.π (g • X) (α.τ g X a) :=
  DFunLike.congr_fun (ρ.covariant g X) a

/-- Symmetries of the target move ambient images exactly as the group moves regions. -/
lemma β_mem_ambient (g : G) {X : R} {b : B} (hb : b ∈ ρ.ambient X) :
    (ρ.β g).1 b ∈ ρ.ambient (g • X) := by
  obtain ⟨a, rfl⟩ := hb
  exact ⟨α.τ g X a, (ρ.covariant_apply g X a).symm⟩

/-- Restriction of a covariant representation to a subgroup. -/
noncomputable def restrictSubgroup (S : Subgroup G) :
    CovariantNetRepresentation (α.restrictSubgroup S) B where
  toNetRepresentation := ρ.toNetRepresentation
  β := ρ.β.comp S.subtype
  covariant g X := ρ.covariant (g : G) X

end CovariantNetRepresentation

end ProbabilisticTheory
