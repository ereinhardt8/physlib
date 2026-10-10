/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.State
public import Mathlib.Algebra.Colimit.Module

/-!

# The global system of local observables

Local observables form one system by identifying each observable with its image in a larger region.

## i. Overview

A measurement supported in a finite region can also be viewed as a measurement in any larger
region. Identifying these descriptions gives a global system of local observables. When the
regions are directed and the net is faithful, this is the algebraic direct limit of the local
systems. Two descriptions agree when they agree in a common larger region; positivity is inherited
from the local systems.

The local systems embed as ordered subsystems. A compatible family of local states is equivalent
to a state on this global system: both give the same expectation value to every local observable.
This is the local-to-global connection needed for thermodynamic limits.

Every element of this construction still has support in some region. No norm completion is taken
here. The construction of a completed quasi-local algebra would require further structure.
Nets and compatible states can also be used without constructing this global system.

## ii. Key results

- `GlobalSystem` : the observables of the whole infinite system, as a direct limit.
- `GlobalSystem.ofChan` : regarding a local observable as an observable of the whole system.
- `GlobalSystem.rep` : the local observables, all realised in the whole system.
- `GlobalSystem.exists_local` : every observable of the whole system is localized somewhere.
- `GlobalSystem.stateEquiv` : states of the whole system are compatible families of local states.

## iii. Table of contents

- A. The underlying vector space
- B. The order
- C. The unit
- D. The canonical representation
- E. States

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped Classical

variable {R : Type*} [PartialOrder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]

/-!

## A. The underlying vector space

-/

namespace LocalNet

/-- The inclusion of a net, as a linear map. -/
def linIncl (N : LocalNet R A) (i j : R) (h : i ≤ j) : A i →ₗ[ℝ] A j := (N.incl h).toLinearMap

instance directedSystem (N : LocalNet R A) : DirectedSystem A (N.linIncl · · ·) where
  map_self := by
    intro i x
    exact N.incl_refl_apply x
  map_map := by
    intro k j i hij hjk x
    exact (N.incl_trans_apply hij hjk x).symm

end LocalNet

/-- The global observable system of a faithful net over directed regions: the direct limit of the
local systems. The faithfulness hypothesis is a parameter so that the order can be an instance. -/
def GlobalSystem (N : LocalNet R A) (_hN : N.IsFaithful) : Type _ :=
  Module.DirectLimit A N.linIncl

namespace GlobalSystem

variable {N : LocalNet R A} {hN : N.IsFaithful}

noncomputable instance : AddCommGroup (GlobalSystem N hN) :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit A N.linIncl))

noncomputable instance : Module ℝ (GlobalSystem N hN) :=
  inferInstanceAs (Module ℝ (Module.DirectLimit A N.linIncl))

/-- The canonical linear map from the local system of `i` to the global system. -/
noncomputable def ofLoc (N : LocalNet R A) (hN : N.IsFaithful) (i : R) :
    A i →ₗ[ℝ] GlobalSystem N hN :=
  Module.DirectLimit.of ℝ R A N.linIncl i

lemma ofLoc_incl {i j : R} (h : i ≤ j) (a : A i) :
    ofLoc N hN j (N.incl h a) = ofLoc N hN i a :=
  Module.DirectLimit.of_f (hij := h) (x := a)

section Directed

variable [IsDirectedOrder R]

/-- Every global observable has a local representative. -/
lemma exists_local [Nonempty R] (x : GlobalSystem N hN) :
    ∃ (i : R) (a : A i), ofLoc N hN i a = x :=
  Module.DirectLimit.exists_of x

lemma exists_local₂ [Nonempty R] (x y : GlobalSystem N hN) :
    ∃ (i : R) (a b : A i), ofLoc N hN i a = x ∧ ofLoc N hN i b = y :=
  Module.DirectLimit.exists_of₂ x y

/-- Global observables are determined by their local representatives. -/
lemma ofLoc_injective (i : R) : Function.Injective (ofLoc N hN i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨j, hij, h⟩ := Module.DirectLimit.of.zero_exact (G := A) (f := N.linIncl) ha
  exact (hN hij).injective (show N.incl hij a = N.incl hij 0 from h.trans (map_zero _).symm)

lemma ofLoc_eq_iff {i j : R} (a : A i) (b : A j) :
    ofLoc N hN i a = ofLoc N hN j b ↔
      ∃ k, ∃ (hik : i ≤ k) (hjk : j ≤ k), N.incl hik a = N.incl hjk b := by
  constructor
  · intro h
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, hik, hjk, ofLoc_injective (N := N) (hN := hN) k ?_⟩
    rw [ofLoc_incl, ofLoc_incl, h]
  · rintro ⟨k, hik, hjk, h⟩
    rw [← ofLoc_incl hik, ← ofLoc_incl hjk, h]

/-!

## B. The order

-/

variable [Nonempty R]

/-- The nonnegative global observables: images of nonnegative local observables. -/
def Pos (N : LocalNet R A) (hN : N.IsFaithful) : Set (GlobalSystem N hN) :=
  {x | ∃ (i : R) (a : A i), 0 ≤ a ∧ ofLoc N hN i a = x}

omit [IsDirectedOrder R] [Nonempty R] in
lemma ofLoc_mem_pos {i : R} {a : A i} (ha : 0 ≤ a) : ofLoc N hN i a ∈ Pos N hN := ⟨i, a, ha, rfl⟩

omit [IsDirectedOrder R] in
lemma zero_mem_pos : (0 : GlobalSystem N hN) ∈ Pos N hN :=
  ⟨Classical.arbitrary R, 0, le_rfl, map_zero _⟩

omit [Nonempty R] in
lemma add_mem_pos {x y : GlobalSystem N hN} (hx : x ∈ Pos N hN) (hy : y ∈ Pos N hN) :
    x + y ∈ Pos N hN := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, rfl⟩ := hy
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, N.incl hik a + N.incl hjk b, add_nonneg (map_nonneg _ ha) (map_nonneg _ hb), ?_⟩
  rw [map_add, ofLoc_incl, ofLoc_incl]

omit [IsDirectedOrder R] [Nonempty R] in
lemma smul_mem_pos {c : ℝ} (hc : 0 ≤ c) {x : GlobalSystem N hN} (hx : x ∈ Pos N hN) :
    c • x ∈ Pos N hN := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  exact ⟨i, c • a, smul_nonneg hc ha, map_smul _ _ _⟩

omit [Nonempty R] in
/-- A global observable that is nonnegative and whose negative is nonnegative vanishes. -/
lemma eq_zero_of_mem_pos_of_neg_mem_pos {x : GlobalSystem N hN} (hx : x ∈ Pos N hN)
    (hx' : -x ∈ Pos N hN) : x = 0 := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, hb'⟩ := hx'
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hsum : N.incl hik a + N.incl hjk b = 0 := by
    apply ofLoc_injective (N := N) (hN := hN) k
    rw [map_add, ofLoc_incl, ofLoc_incl, hb', map_zero, add_neg_cancel]
  have h0 : N.incl hik a = 0 :=
    OrderedVectorSpace.nonneg_add_eq_zero (map_nonneg _ ha) (map_nonneg _ hb) hsum
  rw [← ofLoc_incl hik, h0, map_zero]

noncomputable instance : PartialOrder (GlobalSystem N hN) where
  le x y := y - x ∈ Pos N hN
  le_refl x := by simpa using zero_mem_pos (N := N) (hN := hN)
  le_trans x y z hxy hyz := by
    have := add_mem_pos hxy hyz
    simpa using this
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hxy hyx := by
    have h := eq_zero_of_mem_pos_of_neg_mem_pos hxy (by simpa using hyx)
    exact (sub_eq_zero.1 h).symm

lemma le_def {x y : GlobalSystem N hN} : x ≤ y ↔ y - x ∈ Pos N hN := Iff.rfl

lemma nonneg_iff {x : GlobalSystem N hN} : 0 ≤ x ↔ x ∈ Pos N hN := by
  rw [le_def, sub_zero]

instance : IsOrderedAddMonoid (GlobalSystem N hN) where
  add_le_add_left x y h c := by
    rw [le_def] at h ⊢
    simpa using h

instance : PosSMulMono ℝ (GlobalSystem N hN) where
  smul_le_smul_of_nonneg_left c hc x y h := by
    rw [le_def] at h ⊢
    simpa [smul_sub] using smul_mem_pos hc h

noncomputable instance : OrderedVectorSpace (GlobalSystem N hN) where

/-!

## C. The unit

-/

noncomputable instance : One (GlobalSystem N hN) := ⟨ofLoc N hN (Classical.arbitrary R) 1⟩

/-- Every local unit maps to the global unit. -/
lemma ofLoc_one (i : R) : ofLoc N hN i 1 = (1 : GlobalSystem N hN) := by
  show ofLoc N hN i 1 = ofLoc N hN (Classical.arbitrary R) 1
  rw [ofLoc_eq_iff]
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i (Classical.arbitrary R)
  exact ⟨k, hik, hjk, by rw [map_one, map_one]⟩

noncomputable instance : OrderUnitSpace (GlobalSystem N hN) where
  one_nonneg := by
    rw [nonneg_iff, ← ofLoc_one (Classical.arbitrary R)]
    exact ofLoc_mem_pos OrderUnitSpace.one_nonneg
  exists_nsmul_one_le x := by
    obtain ⟨i, a, rfl⟩ := exists_local x
    obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le a
    refine ⟨n, ?_⟩
    rw [le_def]
    have := ofLoc_mem_pos (N := N) (hN := hN) (sub_nonneg.2 hn)
    rwa [map_sub, map_nsmul, ofLoc_one] at this

/-!

## D. The canonical representation

-/

/-- The canonical channel from the local system of `i` into the global system. -/
noncomputable def ofChan (N : LocalNet R A) (hN : N.IsFaithful) (i : R) :
    Channel (A i) (GlobalSystem N hN) :=
  UnitalPositiveLinearMap.ofLinearMap (ofLoc N hN i) (fun _ ha => nonneg_iff.2 (ofLoc_mem_pos ha))
    (ofLoc_one i)

@[simp] lemma ofChan_apply (i : R) (a : A i) : ofChan N hN i a = ofLoc N hN i a := rfl

/-- The canonical local maps reflect the order: local systems embed as ordered subsystems. -/
lemma ofChan_isOrderEmbedding (i : R) : Channel.IsOrderEmbedding (ofChan N hN i) := by
  rw [Channel.isOrderEmbedding_iff_nonneg]
  intro a ha
  obtain ⟨j, c, hc, hca⟩ := nonneg_iff.1 ha
  obtain ⟨k, hjk, hik, h⟩ := (ofLoc_eq_iff c a).1 hca
  have : 0 ≤ N.incl hik a := h ▸ map_nonneg _ hc
  exact Channel.isOrderEmbedding_iff_nonneg.1 (hN hik) a this

/-- The canonical faithful representation of the net in its global system. -/
noncomputable def rep (N : LocalNet R A) (hN : N.IsFaithful) :
    NetRepresentation N (GlobalSystem N hN) where
  π := ofChan N hN
  π_incl h := UnitalPositiveLinearMap.ext fun a => ofLoc_incl h a

lemma rep_isFaithful : (rep N hN).IsFaithful := ofChan_isOrderEmbedding

/-!

## E. States

-/

/-- The linear functional on the global system determined by a compatible family. -/
noncomputable def liftLin (σ : NetState N) : GlobalSystem N hN →ₗ[ℝ] ℝ :=
  Module.DirectLimit.lift ℝ R A N.linIncl (fun i => (σ.ω i).toLinearMap)
    (fun _ _ hij x => σ.compat_apply hij x)

omit [IsDirectedOrder R] [Nonempty R] in
lemma liftLin_ofLoc (σ : NetState N) (i : R) (a : A i) :
    liftLin (hN := hN) σ (ofLoc N hN i a) = σ.ω i a :=
  Module.DirectLimit.lift_of (fun i => (σ.ω i).toLinearMap)
    (fun _ _ hij x => σ.compat_apply hij x) a

/-- A compatible family of local states, as a state of the global system. -/
noncomputable def ofNetState (σ : NetState N) : 𝓢[ℝ, GlobalSystem N hN] :=
  UnitalPositiveLinearMap.ofLinearMap (liftLin (hN := hN) σ)
    (fun x hx => by
      obtain ⟨i, a, ha, rfl⟩ := nonneg_iff.1 hx
      rw [liftLin_ofLoc (hN := hN)]
      exact map_nonneg (σ.ω i) ha)
    (by
      rw [← ofLoc_one (Classical.arbitrary R), liftLin_ofLoc (hN := hN)]
      exact map_one (σ.ω (Classical.arbitrary R)))

lemma ofNetState_ofLoc (σ : NetState N) (i : R) (a : A i) :
    ofNetState (hN := hN) σ (ofLoc N hN i a) = σ.ω i a :=
  liftLin_ofLoc (hN := hN) σ i a

/-- **Global states are compatible families.** States of the global system are in bijection with
compatible families of local states. -/
noncomputable def stateEquiv : 𝓢[ℝ, GlobalSystem N hN] ≃ NetState N where
  toFun ω := (rep N hN).stateOf ω
  invFun σ := ofNetState σ
  left_inv ω := by
    refine UnitalPositiveLinearMap.ext fun x => ?_
    induction x using Module.DirectLimit.induction_on with
    | ih i a => exact ofNetState_ofLoc (hN := hN) _ i a
  right_inv σ := NetState.ext (funext fun i =>
    UnitalPositiveLinearMap.ext fun a => ofNetState_ofLoc (hN := hN) σ i a)

end Directed

end GlobalSystem

end ProbabilisticTheory
