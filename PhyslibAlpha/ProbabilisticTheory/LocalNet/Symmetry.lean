/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Transport
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!

# Symmetries of an extended system

A group acting on regions and, compatibly, on the observables measurable in them.

## i. Overview

A symmetry group of an extended system, such as the translations of a crystal, rotations
of a lattice or boosts, acts on regions, `X ↦ g • X`. It also acts on observables: a measurement
made in `X` is carried to the same measurement made in the moved region, `τ g X : A X → A (g • X)`.
The usual laws hold:

* doing nothing, `τ 1 X`, changes nothing;
* doing `h` and then `g` is doing `g * h`, `τ (g * h) X = τ g (h • X) ∘ τ h X`;
* moving a region commutes with regarding it as part of a larger one,
  `τ g Y ∘ ι = ι ∘ τ g X`.

This is the *covariance* of the system. It is a property of the system itself and must be kept
apart from invariance of a state (homogeneity) and invariance of the time evolution, which come
later. The action need not be faithful, transitive or abelian.

## ii. Key results

- `RegionAction` : a group moving regions while preserving which lies inside which.
- `EnlargementEquivariant` : moving a region commutes with taking its neighborhood.
- `NetAction` : a group acting on regions and on the observables localized in them.
- `NetAction.symm_eq` : the inverse of moving by `g` is moving by `g⁻¹`.
- `NetAction.restrictSubgroup` : a symmetry group acts through any of its subgroups.
- `NetAction.stabAut` : a symmetry fixing a region acts on the observables inside it.
- `NetAction.restrict_pullback` : moving a state and taking its marginal commute.

## iii. Table of contents

- A. Actions on regions
- B. Actions on nets
- C. Inverses and subgroups
- D. Stabilizers
- E. States
- F. Symmetry of neighborhoods

## iv. References

* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Actions on regions

-/

/-- A group action on regions preserving and reflecting containment. -/
class RegionAction (G R : Type*) [Group G] [PartialOrder R] [MulAction G R] : Prop where
  /-- Group elements preserve and reflect containment. -/
  smul_le_smul_iff : ∀ (g : G) {X Y : R}, g • X ≤ g • Y ↔ X ≤ Y

namespace RegionAction

variable {G R : Type*} [Group G] [PartialOrder R] [MulAction G R] [RegionAction G R]

lemma smul_le_smul (g : G) {X Y : R} (h : X ≤ Y) : g • X ≤ g • Y :=
  (smul_le_smul_iff g).2 h

/-- Restriction to a subgroup is again a region action. -/
instance (S : Subgroup G) : RegionAction S R := ⟨fun g _ _ => smul_le_smul_iff (g : G)⟩

/-- A group action on regions preserves separation. -/
class PreservesSeparation (G R : Type*) [Group G] [PartialOrder R] [MulAction G R]
    [HasSeparation R] : Prop where
  /-- Separation is invariant. -/
  sep_smul_iff : ∀ (g : G) {X Y : R},
    HasSeparation.Sep (g • X) (g • Y) ↔ HasSeparation.Sep X Y

end RegionAction

/-!

## B. Actions on nets

-/

/-- An action of a group `G` on a local net by local isomorphisms. -/
structure NetAction (G : Type*) [Group G] {R : Type*} [PartialOrder R] [MulAction G R]
    [RegionAction G R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)] (N : LocalNet R A) where
  /-- The local isomorphism `A X ≅ A (g • X)`. -/
  τ : ∀ (g : G) (X : R), OrderUnitIso (A X) (A (g • X))
  /-- The identity acts trivially. -/
  τ_one : ∀ X, τ 1 X = eqIso (one_smul G X).symm
  /-- Composition of group elements. -/
  τ_mul : ∀ (g h : G) (X : R),
    τ (g * h) X = (τ h X).trans ((τ g (h • X)).trans (eqIso (mul_smul g h X).symm))
  /-- Compatibility with inclusion. -/
  τ_incl : ∀ (g : G) {X Y : R} (h : X ≤ Y),
    (τ g Y).toChannel.comp (N.incl h)
      = (N.incl (RegionAction.smul_le_smul g h)).comp (τ g X).toChannel

namespace NetAction

variable {G : Type*} [Group G] {R : Type*} [PartialOrder R] [MulAction G R] [RegionAction G R]
  {A : R → Type*} [∀ X, OrderUnitSpace (A X)] {N : LocalNet R A} (α : NetAction G N)

lemma τ_incl_apply (g : G) {X Y : R} (h : X ≤ Y) (a : A X) :
    α.τ g Y (N.incl h a) = N.incl (RegionAction.smul_le_smul g h) (α.τ g X a) :=
  DFunLike.congr_fun (α.τ_incl g h) a

/-- `τ` only depends on the group element, up to transport. -/
lemma τ_congr {g g' : G} (e : g = g') (X : R) :
    α.τ g' X = (α.τ g X).trans (eqIso (congrArg (· • X) e)) := by
  subst e; rfl

/-!

## C. Inverses and subgroups

-/

/-- Transport commutes with the action on regions: conjugating `τ g` by `X = Y`. -/
lemma τ_transport (g : G) {X Y : R} (e : X = Y) :
    (α.τ g X).trans (eqIso (congrArg (g • ·) e)) = (eqIso e).trans (α.τ g Y) := by
  subst e; rfl

/-- The inverse of the local isomorphism `τ g X` is supplied by `g⁻¹`. -/
lemma symm_eq (g : G) (X : R) :
    (α.τ g X).symm = (α.τ g⁻¹ (g • X)).trans (eqIso (inv_smul_smul g X)) := by
  symm
  apply OrderUnitIso.eq_symm_of_trans_eq_refl
  apply OrderUnitIso.trans_right_cancel (e := eqIso (one_smul G X).symm)
  have h1 := α.τ_mul g⁻¹ g X
  have h2 := α.τ_congr (inv_mul_cancel g) X
  rw [α.τ_one, h1] at h2
  rw [OrderUnitIso.refl_trans]
  refine Eq.trans ?_ h2.symm
  simp only [OrderUnitIso.trans_assoc]
  rw [← eqIso_trans, ← eqIso_trans]

/-- Restriction of a net action to a subgroup. -/
def restrictSubgroup (S : Subgroup G) : NetAction S N where
  τ h X := α.τ (h : G) X
  τ_one X := α.τ_one X
  τ_mul g h X := α.τ_mul (g : G) (h : G) X
  τ_incl g _ _ h := α.τ_incl (g : G) h

/-!

## D. Stabilizers

-/

/-- An element stabilizing a region acts internally on its local system. -/
def stabAut (g : G) (X : R) (h : g • X = X) : OrderUnitIso (A X) (A X) :=
  (α.τ g X).trans (eqIso h)

lemma stabAut_one (X : R) : α.stabAut 1 X (one_smul G X) = OrderUnitIso.refl (A X) := by
  unfold stabAut
  rw [α.τ_one, ← eqIso_trans]
  rfl

lemma stabAut_mul (g g' : G) (X : R) (hg : g • X = X) (hg' : g' • X = X)
    (hgg' : (g * g') • X = X) :
    α.stabAut (g * g') X hgg' = (α.stabAut g' X hg').trans (α.stabAut g X hg) := by
  unfold stabAut
  rw [α.τ_mul]
  have key := α.τ_transport g hg'
  have e : (eqIso (A := A) (mul_smul g g' X).symm).trans (eqIso hgg')
      = (eqIso (congrArg (g • ·) hg')).trans (eqIso hg) := by
    rw [← eqIso_trans, ← eqIso_trans]
  simp only [OrderUnitIso.trans_assoc]
  congr 1
  rw [e, ← OrderUnitIso.trans_assoc, key]
  simp only [OrderUnitIso.trans_assoc]

/-- The stabilizer of a region acts on its local system by symmetries. -/
noncomputable def stabHom (X : R) : MulAction.stabilizer G X →* Symmetry (A X) where
  toFun g := (α.stabAut g X g.2).toSymmetry
  map_one' := by
    show (α.stabAut 1 X (one_smul G X)).toSymmetry = 1
    rw [α.stabAut_one]; rfl
  map_mul' g g' := by
    show (α.stabAut (g * g' : G) X _).toSymmetry = _
    rw [α.stabAut_mul g g' X g.2 g'.2 (g * g').2, OrderUnitIso.toSymmetry_trans]

/-!

## E. States

-/

/-- Symmetry and state restriction commute: pulling a state back along `τ g` and restricting to a
smaller region equals restricting first and then pulling back. -/
lemma restrict_pullback (g : G) {X Y : R} (h : X ≤ Y) (ω : 𝓢[ℝ, A (g • Y)]) :
    N.restrict h ((α.τ g Y).pullback ω)
      = (α.τ g X).pullback (N.restrict (RegionAction.smul_le_smul g h) ω) := by
  ext a
  simp [α.τ_incl_apply]

end NetAction

/-!

## F. Symmetry of neighborhoods

-/

/-- Enlargements commute with the group action. -/
class EnlargementEquivariant (G R : Type*) [Group G] [PartialOrder R] [MulAction G R]
    [HasEnlargement R] : Prop where
  /-- Enlarging commutes with moving. -/
  enlarge_smul : ∀ (r : NNReal) (g : G) (X : R),
    HasEnlargement.enlarge r (g • X) = g • HasEnlargement.enlarge r X

end ProbabilisticTheory
