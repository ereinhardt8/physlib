/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.SpinLattice.ClassicalSpins
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.QuantumChannel
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Mathlib.Analysis.Matrix.Order

/-!

# Quantum spins on a lattice

The local observables of a lattice of spin-1/2 particles, and their translation symmetry.

## i. Overview

Place a quantum spin-1/2 on every site of a lattice `S`. The state space of the spins in a finite
set of sites `X` is the space of functions of their `σ^z` configurations `X → Bool`, and the
observables measurable inside `X` are the self-adjoint operators on it: the matrices
`M (c, c')` indexed by pairs of configurations. They contain the spin components `σ^x`, `σ^y`,
`σ^z` at each site of `X`, and all products of them.

An operator of the spins in `X` is also an operator of the spins in a larger region `Y`: it acts as
the given operator on the spins of `X` and as the identity on the others, `M ⊗ 1`. Explicitly
`(M ⊗ 1) (c, c')` is `M (c|X, c'|X)` if the configurations `c` and `c'` agree outside `X`, and `0`
otherwise. This is the inclusion `X ≤ Y` of the net of local observables. It is a unital
`*`-homomorphism of the matrix algebras, hence maps positive operators to positive operators, and
it is injective. The group of lattice symmetries moves the sites and with them the operators.

The functions on configurations of the classical spin lattice sit inside as the diagonal
matrices, the observables that are functions of the `σ^z` only.

## ii. Key results

- `QuantumSpins.inclAlg` : the operator `M ⊗ 1` on a larger region, as a `*`-homomorphism.
- `QuantumSpins.net` : the net of observables of the quantum spins.
- `QuantumSpins.isFaithful` : an operator of a region is distinguishable from others in a larger
  one.

## iii. Table of contents

- A. Spin configurations in a region and gluing
- B. The operator `M ⊗ 1`
- C. The net of local observables
- D. Faithfulness

## iv. References

* R. Haag, Local Quantum Physics, 2nd ed., Chapter III.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd ed.,
  Chapter 6.
-/

@[expose] public section

namespace CondensedMatter

namespace SpinLattice

namespace QuantumSpins

open ProbabilisticTheory
open scoped ComplexOrder Matrix

variable {S : Type*} [DecidableEq S]

/-!

## A. Spin configurations in a region and gluing

-/

/-- The `σ^z` configurations of the spins in a region. -/
abbrev Cfg (X : Finset S) : Type _ := ↥X → Bool

/-- The restriction of a configuration of a region to a subregion. -/
abbrev restr {X Y : Finset S} (h : X ≤ Y) (c : Cfg Y) : Cfg X := fun x => c ⟨x.1, h x.2⟩

/-- Two configurations of a region agree outside a subregion. -/
def Agree {X Y : Finset S} (_h : X ≤ Y) (c c' : Cfg Y) : Prop := ∀ y : ↥Y, y.1 ∉ X → c y = c' y

instance {X Y : Finset S} (h : X ≤ Y) (c c' : Cfg Y) : Decidable (Agree h c c') := by
  unfold Agree; infer_instance

/-- Replace the spins of `c` inside the subregion `X` by those of `a`. -/
def glue {X Y : Finset S} (_h : X ≤ Y) (c : Cfg Y) (a : Cfg X) : Cfg Y :=
  fun y => if hy : y.1 ∈ X then a ⟨y.1, hy⟩ else c y

lemma restr_glue {X Y : Finset S} (h : X ≤ Y) (c : Cfg Y) (a : Cfg X) :
    restr h (glue h c a) = a := by
  funext x; simp [glue, x.2]

lemma agree_glue {X Y : Finset S} (h : X ≤ Y) (c : Cfg Y) (a : Cfg X) :
    Agree h c (glue h c a) := by
  intro y hy; simp [glue, hy]

lemma agree_iff_glue {X Y : Finset S} (h : X ≤ Y) {c c' : Cfg Y} :
    Agree h c c' ↔ glue h c (restr h c') = c' := by
  constructor
  · intro hc
    funext y
    by_cases hy : y.1 ∈ X
    · simp [glue, hy]
    · simp [glue, hy, hc y hy]
  · intro hc y hy
    rw [← hc]; simp [glue, hy]

omit [DecidableEq S] in
lemma agree_refl {X Y : Finset S} (h : X ≤ Y) (c : Cfg Y) : Agree h c c := fun _ _ => rfl

omit [DecidableEq S] in
lemma Agree.symm {X Y : Finset S} {h : X ≤ Y} {c c' : Cfg Y} (hc : Agree h c c') :
    Agree h c' c := fun y hy => (hc y hy).symm

omit [DecidableEq S] in
lemma Agree.trans {X Y : Finset S} {h : X ≤ Y} {c c' c'' : Cfg Y} (hc : Agree h c c')
    (hc' : Agree h c' c'') : Agree h c c'' := fun y hy => (hc y hy).trans (hc' y hy)

lemma eq_of_agree_of_restr_eq {X Y : Finset S} {h : X ≤ Y} {c c' : Cfg Y} (hc : Agree h c c')
    (hr : restr h c = restr h c') : c = c' := by
  funext y
  by_cases hy : y.1 ∈ X
  · exact congrFun hr ⟨y.1, hy⟩
  · exact hc y hy

/-!

## B. The operator `M ⊗ 1`

-/

/-- The operators on the spins of a region: matrices indexed by `σ^z` configurations. -/
abbrev Alg (X : Finset S) : Type _ := Matrix (Cfg X) (Cfg X) ℂ

/-- The operator `M ⊗ 1` on a larger region: `M` on the spins of `X` and the identity on the other
spins. -/
def inclMat {X Y : Finset S} (h : X ≤ Y) (M : Alg X) : Alg Y :=
  Matrix.of fun c c' => if Agree h c c' then M (restr h c) (restr h c') else 0

lemma inclMat_apply {X Y : Finset S} (h : X ≤ Y) (M : Alg X) (c c' : Cfg Y) :
    inclMat h M c c' = if Agree h c c' then M (restr h c) (restr h c') else 0 := rfl

lemma inclMat_one {X Y : Finset S} (h : X ≤ Y) : inclMat h (1 : Alg X) = 1 := by
  ext c c'
  simp only [inclMat_apply, Matrix.one_apply]
  by_cases hc : Agree h c c'
  · by_cases hr : restr h c = restr h c'
    · obtain rfl := eq_of_agree_of_restr_eq hc hr
      simp [hc]
    · have : c ≠ c' := fun e => hr (by rw [e])
      simp [hc, hr, this]
  · have : c ≠ c' := fun e => hc (e ▸ agree_refl h c)
    simp [hc, this]

lemma inclMat_add {X Y : Finset S} (h : X ≤ Y) (M N : Alg X) :
    inclMat h (M + N) = inclMat h M + inclMat h N := by
  ext c c'; simp only [inclMat_apply, Matrix.add_apply]; split_ifs <;> simp

lemma inclMat_smul {X Y : Finset S} (h : X ≤ Y) (r : ℂ) (M : Alg X) :
    inclMat h (r • M) = r • inclMat h M := by
  ext c c'; simp only [inclMat_apply, Matrix.smul_apply]; split_ifs <;> simp

lemma inclMat_conjTranspose {X Y : Finset S} (h : X ≤ Y) (M : Alg X) :
    inclMat h Mᴴ = (inclMat h M)ᴴ := by
  ext c c'
  simp only [inclMat_apply, Matrix.conjTranspose_apply]
  by_cases hc : Agree h c c'
  · simp [hc, hc.symm]
  · have h2 : ¬Agree h c' c := fun h' => hc h'.symm
    simp [hc, h2]

lemma inclMat_mul {X Y : Finset S} (h : X ≤ Y) (M N : Alg X) :
    inclMat h (M * N) = inclMat h M * inclMat h N := by
  ext c c''
  rw [Matrix.mul_apply]
  -- the terms of the sum vanish unless the intermediate configuration agrees with `c`
  set f : Cfg Y → ℂ := fun c' => inclMat h M c c' * inclMat h N c' c'' with hf
  have hsum : ∑ c', f c' = ∑ a : Cfg X, f (glue h c a) := by
    refine Finset.sum_bij_ne_zero (fun c' _ _ => restr h c') (fun _ _ _ => Finset.mem_univ _)
      ?_ ?_ ?_
    · intro c₁ _ h₁ c₂ _ h₂ hr
      have a₁ : Agree h c c₁ := by
        by_contra hc; apply h₁; simp [hf, inclMat_apply, hc]
      have a₂ : Agree h c c₂ := by
        by_contra hc; apply h₂; simp [hf, inclMat_apply, hc]
      exact eq_of_agree_of_restr_eq (a₁.symm.trans a₂) hr
    · intro a _ ha
      exact ⟨glue h c a, Finset.mem_univ _, ha, restr_glue h c a⟩
    · intro c' _ h'
      have hc : Agree h c c' := by
        by_contra hc; apply h'; simp [hf, inclMat_apply, hc]
      rw [(agree_iff_glue h).1 hc]
  rw [hsum]
  have hterm : ∀ a, f (glue h c a)
      = if Agree h c c'' then M (restr h c) a * N a (restr h c'') else 0 := by
    intro a
    have hag : Agree h c (glue h c a) := agree_glue h c a
    simp only [hf, inclMat_apply, hag, ↓reduceIte, restr_glue]
    by_cases hc : Agree h c c''
    · have : Agree h (glue h c a) c'' := hag.symm.trans hc
      simp [hc, this]
    · have : ¬Agree h (glue h c a) c'' := fun h' => hc (hag.trans h')
      simp [hc, this]
  simp only [hterm, inclMat_apply, Matrix.mul_apply]
  split_ifs <;> simp

lemma inclMat_refl {X : Finset S} (M : Alg X) : inclMat (le_refl X) M = M := by
  ext c c'
  have hc : Agree (le_refl X) c c' := fun y hy => absurd y.2 hy
  simp [inclMat_apply, hc]

lemma agree_trans_iff {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (c c' : Cfg Z) :
    Agree (h₁.trans h₂) c c' ↔ Agree h₂ c c' ∧ Agree h₁ (restr h₂ c) (restr h₂ c') := by
  constructor
  · intro hc
    exact ⟨fun z hz => hc z (fun hx => hz (h₁ hx)), fun y hy => hc ⟨y.1, h₂ y.2⟩ hy⟩
  · rintro ⟨hc, hc'⟩ z hz
    by_cases hy : z.1 ∈ Y
    · exact hc' ⟨z.1, hy⟩ hz
    · exact hc z hy

lemma inclMat_trans {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (M : Alg X) :
    inclMat (h₁.trans h₂) M = inclMat h₂ (inclMat h₁ M) := by
  ext c c'
  by_cases h2 : Agree h₂ c c'
  · by_cases h1 : Agree h₁ (restr h₂ c) (restr h₂ c')
    · have h : Agree (h₁.trans h₂) c c' := (agree_trans_iff h₁ h₂ c c').2 ⟨h2, h1⟩
      simp [inclMat_apply, h, h1, h2]
    · have h : ¬Agree (h₁.trans h₂) c c' := fun h => h1 ((agree_trans_iff h₁ h₂ c c').1 h).2
      simp [inclMat_apply, h, h1, h2]
  · have h : ¬Agree (h₁.trans h₂) c c' := fun h => h2 ((agree_trans_iff h₁ h₂ c c').1 h).1
    simp [inclMat_apply, h, h2]

/-- The operator `M ⊗ 1` as a unital `*`-homomorphism. -/
def inclStarAlg {X Y : Finset S} (h : X ≤ Y) : Alg X →⋆ₐ[ℂ] Alg Y where
  toFun := inclMat h
  map_one' := inclMat_one h
  map_mul' := inclMat_mul h
  map_zero' := by ext c c'; simp [inclMat_apply]
  map_add' := inclMat_add h
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rw [← inclMat_one h]; exact inclMat_smul h r 1
  map_star' := inclMat_conjTranspose h

/-!

## C. The net of local observables

-/

/-- The self-adjoint operators on the spins of a region: the observables measurable inside it. -/
abbrev Obs (X : Finset S) : Type _ := selfAdjoint (CStarMatrix (Cfg X) (Cfg X) ℂ)

/-- A unital `*`-homomorphism of C*-algebras induces a channel between their observables. -/
noncomputable def starAlgHomChannel {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →⋆ₐ[ℂ] B) : Channel (selfAdjoint A) (selfAdjoint B) :=
  .ofLinearMap
    { toFun := fun a => ⟨φ (a : A), by
          show star (φ (a : A)) = φ (a : A)
          rw [← map_star, a.2]⟩
      map_add' := fun a b => Subtype.ext <| by
        change φ ((a : A) + b) = φ (a : A) + φ b
        rw [map_add]
      map_smul' := fun r a => Subtype.ext <| by
        change φ ((r : ℂ) • (a : A)) = (r : ℂ) • φ (a : A)
        exact map_smulₛₗ φ (r : ℂ) (a : A) }
    (fun a ha => by
      show (0 : B) ≤ φ (a : A)
      exact map_nonneg φ ha)
    (by
      ext
      change φ (1 : A) = (1 : B)
      exact φ.map_one)

@[simp]
lemma coe_starAlgHomChannel {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (φ : A →⋆ₐ[ℂ] B) (a : selfAdjoint A) :
    (starAlgHomChannel φ a : B) = φ (a : A) := rfl

/-- The inclusion `M ↦ M ⊗ 1`, as a `*`-homomorphism of the C*-algebras of operators. -/
noncomputable def inclC {X Y : Finset S} (h : X ≤ Y) :
    CStarMatrix (Cfg X) (Cfg X) ℂ →⋆ₐ[ℂ] CStarMatrix (Cfg Y) (Cfg Y) ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv : Alg Y ≃⋆ₐ[ℂ] _).toStarAlgHom.comp
    ((inclStarAlg h).comp (CStarMatrix.ofMatrixStarAlgEquiv : Alg X ≃⋆ₐ[ℂ] _).symm.toStarAlgHom)

lemma inclC_apply {X Y : Finset S} (h : X ≤ Y) (M : CStarMatrix (Cfg X) (Cfg X) ℂ) :
    inclC h M = CStarMatrix.ofMatrix (inclMat h (CStarMatrix.ofMatrix.symm M)) := rfl

/-- The net of observables of the quantum spins: the operators of the spins in each region, with
`M ↦ M ⊗ 1` as the inclusion of a smaller region into a larger one. -/
noncomputable def net : LocalNet (Finset S) (Obs (S := S)) where
  incl h := starAlgHomChannel (inclC h)
  incl_refl X := UnitalPositiveLinearMap.ext fun a => Subtype.ext <| by
    simp [inclC_apply, inclMat_refl]
  incl_trans h₁ h₂ := UnitalPositiveLinearMap.ext fun a => Subtype.ext <| by
    change inclC (h₁.trans h₂) (a : CStarMatrix _ _ ℂ)
      = inclC h₂ (inclC h₁ (a : CStarMatrix _ _ ℂ))
    rw [inclC_apply, inclC_apply, inclC_apply, Equiv.symm_apply_apply, inclMat_trans h₁ h₂]

/-!

## D. Faithfulness

-/

/-- In the algebra of operators on the spins of a region, `0 ≤ M` means that `M` is positive
semidefinite. -/
lemma nonneg_iff_posSemidef {n : Type*} [Fintype n] (M : CStarMatrix n n ℂ) :
    0 ≤ M ↔ Matrix.PosSemidef (CStarMatrix.ofMatrix.symm M) := by
  open scoped MatrixOrder in
  rw [← Matrix.nonneg_iff_posSemidef]
  constructor
  · intro h
    rw [StarOrderedRing.nonneg_iff] at h ⊢
    exact h
  · intro h
    rw [StarOrderedRing.nonneg_iff] at h ⊢
    exact h

/-- Compressing `M ⊗ 1` to the configurations that agree with a fixed one outside the region
returns `M`. -/
lemma submatrix_inclMat {X Y : Finset S} (h : X ≤ Y) (c₀ : Cfg Y) (M : Alg X) :
    (inclMat h M).submatrix (glue h c₀) (glue h c₀) = M := by
  ext a a'
  have hag : Agree h (glue h c₀ a) (glue h c₀ a') :=
    (agree_glue h c₀ a).symm.trans (agree_glue h c₀ a')
  simp [inclMat_apply, hag, restr_glue]

/-- **Locality is faithful.** Every inclusion of the quantum spin net is an order embedding: an
operator of the spins in a region is positive as soon as it is positive in a larger region. -/
lemma isFaithful : (net (S := S)).IsFaithful := by
  intro X Y h
  rw [Channel.isOrderEmbedding_iff_nonneg]
  intro a ha
  have h1 : (0 : CStarMatrix (Cfg Y) (Cfg Y) ℂ) ≤ inclC h (a : CStarMatrix (Cfg X) (Cfg X) ℂ) := ha
  rw [nonneg_iff_posSemidef, inclC_apply, Equiv.symm_apply_apply] at h1
  have h2 := h1.submatrix (glue h (fun _ => true))
  rw [submatrix_inclMat] at h2
  show (0 : CStarMatrix (Cfg X) (Cfg X) ℂ) ≤ (a : CStarMatrix (Cfg X) (Cfg X) ℂ)
  exact (nonneg_iff_posSemidef _).2 h2

end QuantumSpins

end SpinLattice

end CondensedMatter
