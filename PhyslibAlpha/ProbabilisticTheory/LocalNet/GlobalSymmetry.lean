/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.GlobalRealization

/-!

# Symmetries of the infinite system

Net symmetries extend to the quasi-local system, and homogeneous states are the same as homogeneous
families of local states.

## i. Overview

The translations of a crystal act on the local observables by moving them,
`τ g X : A X → A (g • X)`. Together these glue to a symmetry `β g` of the quasi-local system of the
infinite crystal, `β g (ofLoc X a) = ofLoc (g • X) (τ g X a)`, so the quasi-local representation is
covariant. Moving a state of the infinite system by `β` corresponds to moving the family of its
local states, and a state of the infinite system is homogeneous exactly when all its local
expectation values are.

## ii. Key results

- `GlobalSystem.globalβ` : the symmetry group acting on the whole system.
- `GlobalSystem.covariantRep` : the local observables in the whole system, with the symmetry
  acting.
- `GlobalSystem.stateEquiv_act` : moving a state of the whole system is moving its local states.
- `GlobalSystem.isInvariant_stateEquiv_iff` : a state of the whole system is homogeneous exactly
  when its family of local states is.

## iii. Table of contents

- A. Extending the local isomorphisms
- B. The covariant representation
- C. States and invariance

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped Classical

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  {N : LocalNet R A} {hN : N.IsFaithful} [IsDirectedOrder R] [Nonempty R]
  {G : Type*} [Group G] [MulAction G R] [RegionAction G R]

namespace GlobalSystem

omit [IsDirectedOrder R] [Nonempty R] in
lemma ofLoc_eqIso {X Y : R} (e : X = Y) (a : A X) :
    ofLoc N hN Y (eqIso e a) = ofLoc N hN X a := by
  subst e; rfl

/-!

## A. Extending the local isomorphisms

-/

/-- The global linear map induced by the local isomorphisms `τ g`. -/
noncomputable def βLin (α : NetAction G N) (g : G) : GlobalSystem N hN →ₗ[ℝ] GlobalSystem N hN :=
  Module.DirectLimit.lift ℝ R A N.linIncl
    (fun i => ofLoc N hN (g • i) ∘ₗ (α.τ g i).toChannel.toLinearMap)
    (fun i j h x => by
      change ofLoc N hN (g • j) (α.τ g j (N.incl h x)) = ofLoc N hN (g • i) (α.τ g i x)
      rw [α.τ_incl_apply, ofLoc_incl])

omit [IsDirectedOrder R] [Nonempty R] in
lemma βLin_ofLoc (α : NetAction G N) (g : G) (i : R) (a : A i) :
    βLin α g (ofLoc N hN i a) = ofLoc N hN (g • i) (α.τ g i a) :=
  Module.DirectLimit.lift_of _ _ a

/-- The extended map of a group element, as a channel of the global system. -/
noncomputable def βChan (α : NetAction G N) (g : G) :
    Channel (GlobalSystem N hN) (GlobalSystem N hN) :=
  UnitalPositiveLinearMap.ofLinearMap (βLin α g)
    (fun x hx => by
      obtain ⟨i, a, ha, rfl⟩ := nonneg_iff.1 hx
      rw [βLin_ofLoc]
      exact nonneg_iff.2 (ofLoc_mem_pos (map_nonneg (α.τ g i).toChannel ha)))
    (by
      have h1 : (α.τ g (Classical.arbitrary R)) 1 = 1 :=
        map_one (α.τ g (Classical.arbitrary R)).toChannel
      conv_lhs => rw [← ofLoc_one (hN := hN) (Classical.arbitrary R)]
      rw [βLin_ofLoc, h1, ofLoc_one])

lemma βChan_apply_ofLoc (α : NetAction G N) (g : G) (i : R) (a : A i) :
    βChan (hN := hN) α g (ofLoc N hN i a) = ofLoc N hN (g • i) (α.τ g i a) :=
  βLin_ofLoc α g i a

lemma βChan_one (α : NetAction G N) :
    βChan (hN := hN) α 1 = .id ℝ (GlobalSystem N hN) := by
  refine UnitalPositiveLinearMap.ext fun x => ?_
  induction x using Module.DirectLimit.induction_on with
  | ih i a =>
    change βChan (hN := hN) α 1 (ofLoc N hN i a) = ofLoc N hN i a
    rw [βChan_apply_ofLoc, α.τ_one, ofLoc_eqIso]

lemma βChan_mul (α : NetAction G N) (g h : G) :
    βChan (hN := hN) α (g * h) = (βChan α g).comp (βChan α h) := by
  refine UnitalPositiveLinearMap.ext fun x => ?_
  induction x using Module.DirectLimit.induction_on with
  | ih i a =>
    change βChan (hN := hN) α (g * h) (ofLoc N hN i a)
      = βChan α g (βChan α h (ofLoc N hN i a))
    rw [βChan_apply_ofLoc (hN := hN), βChan_apply_ofLoc (hN := hN), βChan_apply_ofLoc (hN := hN),
      α.τ_mul]
    exact ofLoc_eqIso _ _

/-- The extended symmetry of a group element. -/
noncomputable def βSym (α : NetAction G N) (g : G) : Symmetry (GlobalSystem N hN) :=
  ⟨βChan α g, βChan α g⁻¹, by rw [← βChan_mul, inv_mul_cancel, βChan_one],
    by rw [← βChan_mul, mul_inv_cancel, βChan_one]⟩

/-- Net symmetries extend to a group of symmetries of the global system. -/
noncomputable def globalβ (α : NetAction G N) : G →* Symmetry (GlobalSystem N hN) where
  toFun := βSym α
  map_one' := Subtype.ext (βChan_one α)
  map_mul' g h := Subtype.ext (βChan_mul α g h)

/-!

## B. The covariant representation

-/

/-- The canonical representation of a net in its global system is covariant. -/
noncomputable def covariantRep (α : NetAction G N) :
    CovariantNetRepresentation α (GlobalSystem N hN) where
  toNetRepresentation := rep N hN
  β := globalβ α
  covariant g X := UnitalPositiveLinearMap.ext fun a => βChan_apply_ofLoc α g X a

/-!

## C. States and invariance

-/

lemma stateEquiv_act (α : NetAction G N) (g : G) (ω : 𝓢[ℝ, GlobalSystem N hN]) :
    stateEquiv (globalβ α g • ω) = NetState.act α g (stateEquiv ω) := by
  refine NetState.ext (funext fun i => UnitalPositiveLinearMap.ext fun a => ?_)
  change ((ω.comp (globalβ α g)⁻¹.1).comp (ofChan N hN i)) a
    = (NetState.act α g (stateEquiv ω)).ω i a
  rw [← map_inv]
  exact congrArg ω (βChan_apply_ofLoc α g⁻¹ i a)

/-- **Compatible local states, global realization and symmetry invariance.** A state of the global
system is invariant under the extended symmetries exactly when its compatible family of local
states is invariant under the net action. -/
theorem isInvariant_stateEquiv_iff (α : NetAction G N) (ω : 𝓢[ℝ, GlobalSystem N hN]) :
    NetState.IsInvariant α (stateEquiv ω) ↔ ∀ g : G, ω.comp (globalβ α g).1 = ω := by
  refine ⟨fun h g => ?_, fun h => (covariantRep α).isInvariant_stateOf h⟩
  refine UnitalPositiveLinearMap.ext fun x => ?_
  induction x using Module.DirectLimit.induction_on with
  | ih i a =>
    have h' := DFunLike.congr_fun (h g i) a
    change ω ((globalβ α g).1 (ofLoc N hN i a)) = ω (ofLoc N hN i a)
    rw [show (globalβ α g).1 (ofLoc N hN i a) = ofLoc N hN (g • i) (α.τ g i a) from
      βChan_apply_ofLoc α g i a]
    exact h'

end GlobalSystem

end ProbabilisticTheory
