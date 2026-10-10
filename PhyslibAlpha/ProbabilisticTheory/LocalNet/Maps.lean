/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Channel.Symmetry

/-!

# Maps between observable systems

Transformations that respect what can be measured: restriction to a subsystem and reversible
changes of description.

## i. Overview

The measurable quantities of a physical system form a real vector space with an order: an
observable is positive if every measurement of it gives a nonnegative number. The certain outcome
is a distinguished observable `1`. A map between two such systems that is physically meaningful
sends positive observables to positive observables and the certain outcome to the certain outcome.
This is a `Channel`: the Heisenberg-picture form of a transformation of states.

Three kinds of channel occur when a system is assembled from its parts:

* an *embedding*, which regards a measurement made in a small region as a measurement made in a
  larger one. It loses nothing: it also reflects the order, so observables that compare as `≤` in
  the larger system already compared so in the smaller one;
* an *isomorphism*, a reversible change of description such as moving a region by a translation,
  whose inverse is again a channel;
* a *symmetry*, an isomorphism of a system with itself.

No lattice structure is assumed on the observables, since the observables of a quantum system
do not have one.

## ii. Key results

- `Channel.IsOrderEmbedding` : the channel loses no information about the order of observables.
- `Channel.IsOrderEmbedding.injective` : an embedding distinguishes all the observables it
  embeds.
- `OrderUnitIso` : a reversible change of description of a system.
- `OrderUnitIso.refl`, `.symm`, `.trans` : doing nothing, undoing, and composing changes of
  description.
- `OrderUnitIso.toSymmetry` : a reversible change of a system into itself is a symmetry.

## iii. Table of contents

- A. Order embeddings
- B. Order-unit isomorphisms
- C. Automorphisms and symmetries

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Order embeddings

-/

namespace Channel

variable {E F G : Type*} [OrderUnitSpace E] [OrderUnitSpace F] [OrderUnitSpace G]

/-- A channel is an order embedding when it reflects the order: `φ a ≤ φ b` implies `a ≤ b`.
Together with monotonicity this makes `E` an ordered subsystem of `F`, as opposed to a quotient. -/
def IsOrderEmbedding (φ : Channel E F) : Prop := ∀ a b, φ a ≤ φ b → a ≤ b

lemma IsOrderEmbedding.le_iff {φ : Channel E F} (h : IsOrderEmbedding φ) {a b : E} :
    φ a ≤ φ b ↔ a ≤ b :=
  ⟨h a b, fun hab => OrderHomClass.mono φ hab⟩

/-- A linear channel reflects the order exactly when it reflects positivity. -/
lemma isOrderEmbedding_iff_nonneg {φ : Channel E F} :
    IsOrderEmbedding φ ↔ ∀ a, 0 ≤ φ a → 0 ≤ a := by
  refine ⟨fun h a ha => h 0 a (by simpa using ha), fun h a b hab => ?_⟩
  have : 0 ≤ φ (b - a) := by rw [map_sub]; exact sub_nonneg.2 hab
  exact sub_nonneg.1 (h _ this)

/-- An order embedding is injective. -/
lemma IsOrderEmbedding.injective {φ : Channel E F} (h : IsOrderEmbedding φ) :
    Function.Injective φ :=
  fun a b hab => le_antisymm (h a b hab.le) (h b a hab.ge)

lemma isOrderEmbedding_id : IsOrderEmbedding (.id ℝ E : Channel E E) := fun _ _ h => h

lemma IsOrderEmbedding.comp {ψ : Channel F G} {φ : Channel E F} (hψ : IsOrderEmbedding ψ)
    (hφ : IsOrderEmbedding φ) : IsOrderEmbedding (ψ.comp φ) :=
  fun a b h => hφ a b (hψ _ _ h)

end Channel

/-!

## B. Order-unit isomorphisms

-/

/-- An isomorphism of order-unit spaces: a channel bundled with a channel that is a two-sided
inverse. Both directions are positive and unital. -/
structure OrderUnitIso (E F : Type*) [OrderUnitSpace E] [OrderUnitSpace F] where
  /-- The forward channel. -/
  toChannel : Channel E F
  /-- The inverse channel. -/
  invChannel : Channel F E
  /-- The inverse followed by the forward map is the identity on `F`. -/
  comp_inv : toChannel.comp invChannel = .id ℝ F
  /-- The forward map followed by the inverse is the identity on `E`. -/
  inv_comp : invChannel.comp toChannel = .id ℝ E

namespace OrderUnitIso

variable {E F G H : Type*} [OrderUnitSpace E] [OrderUnitSpace F] [OrderUnitSpace G]
  [OrderUnitSpace H]

instance : FunLike (OrderUnitIso E F) E F where
  coe e := e.toChannel
  coe_injective e e' h := by
    have h1 : e.toChannel = e'.toChannel := UnitalPositiveLinearMap.ext (congrFun h)
    have h2 : e.invChannel = e'.invChannel := by
      calc e.invChannel = e.invChannel.comp (e'.toChannel.comp e'.invChannel) := by
            rw [e'.comp_inv, UnitalPositiveLinearMap.comp_id]
        _ = (e.invChannel.comp e.toChannel).comp e'.invChannel := by
            rw [← h1, UnitalPositiveLinearMap.comp_assoc]
        _ = e'.invChannel := by rw [e.inv_comp, UnitalPositiveLinearMap.id_comp]
    cases e; cases e'; simp_all

@[ext]
lemma ext {e e' : OrderUnitIso E F} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

@[simp] lemma coe_toChannel (e : OrderUnitIso E F) (x : E) : e.toChannel x = e x := rfl

@[simp] lemma invChannel_apply_apply (e : OrderUnitIso E F) (x : E) : e.invChannel (e x) = x :=
  by simpa using DFunLike.congr_fun e.inv_comp x

@[simp] lemma apply_invChannel_apply (e : OrderUnitIso E F) (y : F) : e (e.invChannel y) = y :=
  by simpa using DFunLike.congr_fun e.comp_inv y

/-- The identity isomorphism. -/
def refl (E : Type*) [OrderUnitSpace E] : OrderUnitIso E E where
  toChannel := .id ℝ E
  invChannel := .id ℝ E
  comp_inv := UnitalPositiveLinearMap.id_comp _
  inv_comp := UnitalPositiveLinearMap.id_comp _

@[simp] lemma refl_apply (x : E) : refl E x = x := rfl

/-- The inverse isomorphism. -/
def symm (e : OrderUnitIso E F) : OrderUnitIso F E where
  toChannel := e.invChannel
  invChannel := e.toChannel
  comp_inv := e.inv_comp
  inv_comp := e.comp_inv

@[simp] lemma symm_apply (e : OrderUnitIso E F) (y : F) : e.symm y = e.invChannel y := rfl

@[simp] lemma symm_symm (e : OrderUnitIso E F) : e.symm.symm = e := rfl

/-- Composition of isomorphisms. -/
def trans (e : OrderUnitIso E F) (e' : OrderUnitIso F G) : OrderUnitIso E G where
  toChannel := e'.toChannel.comp e.toChannel
  invChannel := e.invChannel.comp e'.invChannel
  comp_inv := by
    ext y; simp
  inv_comp := by
    ext x; simp

@[simp] lemma trans_apply (e : OrderUnitIso E F) (e' : OrderUnitIso F G) (x : E) :
    e.trans e' x = e' (e x) := rfl

@[simp] lemma refl_trans (e : OrderUnitIso E F) : (refl E).trans e = e := rfl

@[simp] lemma trans_refl (e : OrderUnitIso E F) : e.trans (refl F) = e := rfl

lemma trans_assoc (e : OrderUnitIso E F) (e' : OrderUnitIso F G) (e'' : OrderUnitIso G H) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') := rfl

@[simp] lemma symm_trans_self (e : OrderUnitIso E F) : e.symm.trans e = refl F :=
  ext fun y => e.apply_invChannel_apply y

@[simp] lemma self_trans_symm (e : OrderUnitIso E F) : e.trans e.symm = refl E :=
  ext fun x => e.invChannel_apply_apply x

/-- If `e'` undoes `e`, then `e'` is the inverse of `e`. -/
lemma eq_symm_of_trans_eq_refl {e : OrderUnitIso E F} {e' : OrderUnitIso F E}
    (h : e.trans e' = refl E) : e' = e.symm := by
  ext y
  have := congrArg (fun k => k (e.invChannel y)) h
  simp only [trans_apply, refl_apply, apply_invChannel_apply] at this
  simpa using this

/-- Isomorphisms can be cancelled on the left. -/
lemma trans_left_cancel {e : OrderUnitIso E F} {a b : OrderUnitIso F G}
    (h : e.trans a = e.trans b) : a = b := by
  ext y
  have := congrArg (fun k => k (e.invChannel y)) h
  simpa using this

/-- Isomorphisms can be cancelled on the right. -/
lemma trans_right_cancel {e : OrderUnitIso F G} {a b : OrderUnitIso E F}
    (h : a.trans e = b.trans e) : a = b := by
  ext x
  have h' : e (a x) = e (b x) := by simpa using congrArg (fun k => k x) h
  simpa using congrArg e.invChannel h'

lemma bijective (e : OrderUnitIso E F) : Function.Bijective e :=
  ⟨Function.LeftInverse.injective e.invChannel_apply_apply,
    Function.RightInverse.surjective e.apply_invChannel_apply⟩

/-- An isomorphism is an order embedding. -/
lemma isOrderEmbedding (e : OrderUnitIso E F) : Channel.IsOrderEmbedding e.toChannel :=
  fun a b h => by simpa using OrderHomClass.mono e.invChannel h

/-- The pullback of a state along an isomorphism. -/
def pullback (e : OrderUnitIso E F) (ω : 𝓢[ℝ, F]) : 𝓢[ℝ, E] := ω.comp e.toChannel

@[simp] lemma pullback_apply (e : OrderUnitIso E F) (ω : 𝓢[ℝ, F]) (x : E) :
    e.pullback ω x = ω (e x) := rfl

lemma pullback_trans (e : OrderUnitIso E F) (e' : OrderUnitIso F G) (ω : 𝓢[ℝ, G]) :
    (e.trans e').pullback ω = e.pullback (e'.pullback ω) := rfl

/-!

## C. Automorphisms and symmetries

-/

/-- An automorphism of `E` is a symmetry. -/
def toSymmetry (e : OrderUnitIso E E) : Symmetry E :=
  ⟨e.toChannel, e.invChannel, e.inv_comp, e.comp_inv⟩

/-- Every symmetry is an automorphism, using its chosen inverse. -/
noncomputable def ofSymmetry (φ : Symmetry E) : OrderUnitIso E E where
  toChannel := φ.1
  invChannel := φ.2.inverse
  comp_inv := φ.2.comp_inverse
  inv_comp := φ.2.inverse_comp

/-- Composition of automorphisms is multiplication in the opposite order, as for functions. -/
lemma toSymmetry_trans (e e' : OrderUnitIso E E) :
    (e.trans e').toSymmetry = e'.toSymmetry * e.toSymmetry := rfl

@[simp] lemma toSymmetry_refl : (refl E).toSymmetry = 1 := rfl

@[simp] lemma toSymmetry_ofSymmetry (φ : Symmetry E) : (ofSymmetry φ).toSymmetry = φ := rfl

@[simp] lemma ofSymmetry_apply (φ : Symmetry E) (x : E) : ofSymmetry φ x = φ.1 x := rfl

end OrderUnitIso

end ProbabilisticTheory
