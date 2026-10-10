/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.LocalNet.Symmetry
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!

# Lattice systems

Finite sets of sites as regions, a group acting on sites, disjointness as separation, and neighbors.

## i. Overview

For a lattice system, such as a crystal or a lattice of spins, the regions are finite sets
of sites ordered by inclusion. A group acting on the sites, for instance the translations of the
lattice, moves whole regions and preserves which lies inside which. Two regions are separated when
they have no site in common. Nearby sites are described by a neighbor structure, from which
enlargement of a region by a radius is built. For a periodic pattern one takes the sites to be
`Λ × B` with translations of `Λ` acting on the first factor, `B` being the contents of a unit
cell; nothing here requires this form, so non-rectangular lattices are included.

Restricting to a finite box and imposing periodic identification of its boundary are different
constructions with different physics. Only the first is treated in this file.

## ii. Key results

- `Lattice.regionAction` : translating a finite set of sites.
- `Lattice.disjointSeparation` : regions with no common site are separated, and translation
  preserves this.
- `Lattice.Neighborhoods` : which sites lie within a given radius of a site.
- `Lattice.Neighborhoods.hasEnlargement` : the enlargement of a finite region by a radius.
- `Lattice.Neighborhoods.enlargementEquivariant` : translating commutes with enlarging.

## iii. Table of contents

- A. Regions and the group action
- B. Separation
- C. Neighbor data and enlargement

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.
* E. Lieb & D. Robinson, The finite group velocity of quantum spin systems.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace Lattice

open scoped Pointwise

variable (G S : Type*) [Group G] [MulAction G S] [DecidableEq S]

/-!

## A. Regions and the group action

-/

instance regionAction : RegionAction G (Finset S) :=
  ⟨fun _ _ _ => Finset.smul_finset_subset_smul_finset_iff⟩

/-!

## B. Separation

-/

/-- Two finite regions are separated when they are disjoint. -/
instance disjointSeparation : HasSeparation (Finset S) where
  Sep X Y := Disjoint X Y
  symm h := h.symm
  mono h hX hY := h.mono hX hY

/-- The group action preserves and reflects disjointness. -/
instance preservesSeparation : RegionAction.PreservesSeparation G (Finset S) where
  sep_smul_iff g _ _ := Finset.disjoint_image (MulAction.injective g)

/-!

## C. Neighbor data and enlargement

-/

/-- Neighbor data on a set of sites: `nbhd r s` is the finite set of sites within radius `r` of
`s`. -/
structure Neighborhoods (S : Type*) [DecidableEq S] where
  /-- The sites within radius `r` of `s`. -/
  nbhd : NNReal → S → Finset S
  /-- A site is within every radius of itself. -/
  mem_nbhd_self : ∀ r s, s ∈ nbhd r s
  /-- Radius `0` sees only the site itself. -/
  nbhd_zero : ∀ s, nbhd 0 s = {s}
  /-- Larger radii see more. -/
  nbhd_mono : ∀ {r r' : NNReal}, r ≤ r' → ∀ s, nbhd r s ⊆ nbhd r' s
  /-- The triangle inequality. -/
  nbhd_trans : ∀ (r s : NNReal) {a b c : S}, b ∈ nbhd s a → c ∈ nbhd r b → c ∈ nbhd (r + s) a

namespace Neighborhoods

variable {S G} (nb : Neighborhoods S)

/-- Enlargement of a finite region by a radius: all sites within that radius of the region. -/
def enlarge (r : NNReal) (X : Finset S) : Finset S := X.biUnion (nb.nbhd r)

lemma mem_enlarge {r : NNReal} {X : Finset S} {c : S} :
    c ∈ nb.enlarge r X ↔ ∃ a ∈ X, c ∈ nb.nbhd r a := by
  simp [enlarge]

/-- Neighbor data gives enlargements of finite regions. -/
abbrev hasEnlargement : HasEnlargement (Finset S) where
  enlarge := nb.enlarge
  enlarge_zero X := by
    ext c
    simp [mem_enlarge, nb.nbhd_zero]
  enlarge_add_le r s X c hc := by
    obtain ⟨b, hb, hcb⟩ := (mem_enlarge nb).1 hc
    obtain ⟨a, ha, hba⟩ := (mem_enlarge nb).1 hb
    exact (mem_enlarge nb).2 ⟨a, ha, nb.nbhd_trans r s hba hcb⟩
  enlarge_mono r X Y h c hc := by
    obtain ⟨a, ha, hca⟩ := (mem_enlarge nb).1 hc
    exact (mem_enlarge nb).2 ⟨a, h ha, hca⟩
  enlarge_mono_radius h X c hc := by
    obtain ⟨a, ha, hca⟩ := (mem_enlarge nb).1 hc
    exact (mem_enlarge nb).2 ⟨a, ha, nb.nbhd_mono h a hca⟩

/-- The neighbor data is equivariant under the group action. -/
def IsEquivariant (G : Type*) [Group G] [MulAction G S] : Prop :=
  ∀ (r : NNReal) (g : G) (s : S), nb.nbhd r (g • s) = g • nb.nbhd r s

/-- Enlargement of finite regions commutes with the group action when the neighbor data is
equivariant. -/
lemma enlargementEquivariant (h : nb.IsEquivariant G) :
    @EnlargementEquivariant G (Finset S) _ _ _ nb.hasEnlargement :=
  @EnlargementEquivariant.mk G (Finset S) _ _ _ nb.hasEnlargement fun r g X => by
    ext c
    change c ∈ nb.enlarge r (g • X) ↔ c ∈ g • nb.enlarge r X
    rw [mem_enlarge, Finset.mem_smul_finset]
    constructor
    · rintro ⟨a, ha, hca⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 ha
      rw [h r g x] at hca
      obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hca
      exact ⟨y, (mem_enlarge nb).2 ⟨x, hx, hy⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hyx⟩ := (mem_enlarge nb).1 hy
      refine ⟨g • x, Finset.smul_mem_smul_finset hx, ?_⟩
      rw [h r g x]
      exact Finset.smul_mem_smul_finset hyx

end Neighborhoods

end Lattice

end ProbabilisticTheory
