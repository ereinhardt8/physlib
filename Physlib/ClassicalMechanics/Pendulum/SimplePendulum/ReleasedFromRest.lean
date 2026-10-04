/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.SmallAngle
/-!

# The simple pendulum released from rest

## i. Overview

This module collects what is known about the simple pendulum released from rest at an angle
`θ₀`, across both the exact nonlinear dynamics and the small-angle approximation.

For the exact equation of motion, this module begins the identification of
`SimplePendulum.periodFormula` with the actual period of the nonlinear pendulum, the theorem
left open by `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.PeriodFormula`. The classical
argument (Landau & Lifshitz, §11, Problem 1) starts from the energy first integral: multiplying
the equation of motion by the angular velocity and integrating once, using energy conservation,
gives `θ̇² = (2g/ℓ)(cos θ - cos θ₀)` along a solution released from rest at the angle `θ₀`. That
quadrature is proved here. It is purely algebraic — a rearrangement of
`SimplePendulum.energy_conservation_of_equationOfMotion'` together with the initial data of a
motion released from rest — and does not yet touch the harder analytic content of the classical
argument: the quarter period as a first hitting time, the further substitution turning the
quadrature into `SimplePendulum.periodFormula`, and the identification of the resulting period
with a genuine (globally defined) solution. Those remain open; see the module docstring of
`PeriodFormula` for the full list of milestones.

For the small-angle approximation, this module also records the linearized motion released from
rest, the cosine `θ₀ cos (ω t)`: its identification with the small-angle trajectory of the
corresponding initial data, its initial angle and vanishing initial angular velocity, and its
dynamics — satisfying the linearized equation of motion and being periodic with the small-angle
period.

## ii. Key results

- `SimplePendulum.inertia_mul_sq_deriv_eq_of_isSolution_of_deriv_zero`: along a solution `θ` of
  the exact equation of motion with `θ 0 0 = θ₀` and released from rest,
  `I θ̇² = 2 m g ℓ (cos θ - cos θ₀)` at every instant.
- `SimplePendulum.sq_deriv_eq_of_isSolution_of_deriv_zero`: the same identity with the mass and
  moment of inertia cancelled, `θ̇² = 2 ω² (cos θ - cos θ₀)`.
- `SimplePendulum.sq_deriv_eq_of_isSolution_of_deriv_zero'`: the classical form,
  `θ̇² = (2 g / ℓ) (cos θ - cos θ₀)`.
- `SimplePendulum.releasedFromRest` is the small-angle motion released from rest at angle `θ₀`,
  the cosine `θ₀ cos (ω t)`, identified with the small-angle trajectory of the corresponding
  initial data by `releasedFromRest_eq`, with its initial data recorded by
  `releasedFromRest_at_zero` and `releasedFromRest_velocity_at_zero`, and its dynamics by
  `releasedFromRest_linearizedEquationOfMotion` and `releasedFromRest_periodic`.

## iii. Table of contents

- A. The energy first integral of a motion released from rest
- B. The linearized motion released from rest
  - B.1. The motion and its identification with the small-angle trajectory
  - B.2. Initial data and dynamics

## iv. References

- Landau & Lifshitz, Mechanics, 3rd ed., §11, Problem 1 (the quadrature of the energy first
  integral on the descent).
- The module `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.PeriodFormula`, for the theorem
  this quadrature is a first step towards.
- The module `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.SmallAngle`, for the small-angle
  approximation and its solution theory, of which section B is a specialization.

-/

@[expose] public section

namespace ClassicalMechanics
open Real InnerProductSpace Time
open scoped ContDiff

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

## A. The energy first integral of a motion released from rest

A solution released from rest at the angle `θ₀` has, at the initial instant, vanishing kinetic
energy and potential energy `m g ℓ (1 - cos θ₀)`; by energy conservation this total is carried
unchanged to every later instant, and reading off the kinetic energy there gives the quadrature.
The computation is the same rearrangement used throughout `SimplePendulum.Basic`, so no new
analytic input is needed here, only the two special values of the energy at time `0`.

-/

/-- Along a solution of the simple pendulum with `θ 0 0 = θ₀` and released from rest,
  `∂ₜ θ 0 = 0`, the energy first integral holds at every instant in the form
  `I θ̇² = 2 m g ℓ (cos θ - cos θ₀)`, with the moment of inertia `I` and the mass `m` not yet
  cancelled. This is read off from energy conservation (`IsSolution.energy_eq`) at the two
  special values of the energy at time `0`: zero kinetic energy and potential energy
  `m g ℓ (1 - cos θ₀)`. -/
lemma inertia_mul_sq_deriv_eq_of_isSolution_of_deriv_zero
    {θ : Time → EuclideanSpace ℝ (Fin 1)} {θ₀ : ℝ} (h : S.IsSolution θ) (hx0 : θ 0 0 = θ₀)
    (hv0 : ∂ₜ θ 0 = 0) (t : Time) :
    S.inertia * (∂ₜ θ t 0) ^ 2 = 2 * (S.m * S.g * S.ℓ) * (Real.cos (θ t 0) - Real.cos θ₀) := by
  have hE := h.energy_eq t
  simp only [energy_eq, kineticEnergy_eq, potentialEnergy_eq, hv0, hx0, inner_zero_left,
    mul_zero, zero_add] at hE
  rw [PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply, conj_trivial] at hE
  linear_combination 2 * hE

/-- Along a solution of the simple pendulum with `θ 0 0 = θ₀` and released from rest,
  `∂ₜ θ 0 = 0`, the energy first integral holds with the mass cancelled,
  `θ̇² = 2 ω² (cos θ - cos θ₀)`, where `ω = √(g/ℓ)`. -/
lemma sq_deriv_eq_of_isSolution_of_deriv_zero
    {θ : Time → EuclideanSpace ℝ (Fin 1)} {θ₀ : ℝ} (h : S.IsSolution θ) (hx0 : θ 0 0 = θ₀)
    (hv0 : ∂ₜ θ 0 = 0) (t : Time) :
    (∂ₜ θ t 0) ^ 2 = 2 * S.ω ^ 2 * (Real.cos (θ t 0) - Real.cos θ₀) := by
  have hkey := S.inertia_mul_sq_deriv_eq_of_isSolution_of_deriv_zero h hx0 hv0 t
  have h' : S.inertia * ((∂ₜ θ t 0) ^ 2 - 2 * S.ω ^ 2 * (Real.cos (θ t 0) - Real.cos θ₀)) = 0 := by
    linear_combination hkey - 2 * (Real.cos (θ t 0) - Real.cos θ₀) * S.ω_sq_mul_inertia
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left S.inertia_ne_zero)

/-- Along a solution of the simple pendulum with `θ 0 0 = θ₀` and released from rest,
  `∂ₜ θ 0 = 0`, the energy first integral in the classical `g / ℓ` form:
  `θ̇² = (2 g / ℓ) (cos θ - cos θ₀)`. -/
lemma sq_deriv_eq_of_isSolution_of_deriv_zero'
    {θ : Time → EuclideanSpace ℝ (Fin 1)} {θ₀ : ℝ} (h : S.IsSolution θ) (hx0 : θ 0 0 = θ₀)
    (hv0 : ∂ₜ θ 0 = 0) (t : Time) :
    (∂ₜ θ t 0) ^ 2 = 2 * (S.g / S.ℓ) * (Real.cos (θ t 0) - Real.cos θ₀) := by
  rw [S.sq_deriv_eq_of_isSolution_of_deriv_zero h hx0 hv0 t, S.ω_sq]

/-!

## B. The linearized motion released from rest

The classical small-angle experiment: the pendulum is displaced to an angle `θ₀` and released
from rest. Its small-angle motion is the cosine `θ₀ cos (ω t)`, the small-angle trajectory of
the initial conditions with initial angle `θ₀` and zero initial angular velocity; it starts at
the angle `θ₀` with vanishing angular velocity, and satisfies the linearized equation of
motion.

-/

/-!

### B.1. The motion and its identification with the small-angle trajectory

-/

/-- The small-angle motion of the pendulum released from rest at initial angle `θ₀`: the
  cosine `θ₀ cos (ω t)` of angular frequency `ω`. -/
noncomputable def releasedFromRest (θ₀ : ℝ) : Time → EuclideanSpace ℝ (Fin 1) :=
  fun t => Real.cos (S.ω * t.val) • EuclideanSpace.single (0 : Fin 1) θ₀

/-- The motion released from rest at angle `θ₀` is the small-angle trajectory of the initial
  conditions with initial angle `θ₀` and zero initial angular velocity. -/
lemma releasedFromRest_eq (θ₀ : ℝ) :
    S.releasedFromRest θ₀ = S.smallAngleTrajectory ⟨EuclideanSpace.single 0 θ₀, 0⟩ := by
  funext t
  ext i
  simp [releasedFromRest, smallAngleTrajectory,
    HarmonicOscillator.InitialConditions.trajectory, toHarmonicOscillator_ω]

/-!

### B.2. Initial data and dynamics

-/

/-- At time `0` the motion released from rest at angle `θ₀` is at the angle `θ₀`. -/
@[simp]
lemma releasedFromRest_at_zero (θ₀ : ℝ) :
    S.releasedFromRest θ₀ 0 = EuclideanSpace.single 0 θ₀ := by
  simp [releasedFromRest]

/-- The motion released from rest at angle `θ₀` is genuinely released from rest: its angular
  velocity at time `0` vanishes. -/
@[simp]
lemma releasedFromRest_velocity_at_zero (θ₀ : ℝ) : ∂ₜ (S.releasedFromRest θ₀) 0 = 0 := by
  rw [S.releasedFromRest_eq θ₀]
  exact S.smallAngleTrajectory_velocity_at_zero ⟨EuclideanSpace.single 0 θ₀, 0⟩

/-- The motion released from rest at angle `θ₀` satisfies the linearized equation of
  motion. -/
lemma releasedFromRest_linearizedEquationOfMotion (θ₀ : ℝ) :
    S.LinearizedEquationOfMotion (S.releasedFromRest θ₀) := by
  rw [S.releasedFromRest_eq θ₀]
  exact S.smallAngleTrajectory_linearizedEquationOfMotion ⟨EuclideanSpace.single 0 θ₀, 0⟩

/-- The motion released from rest at angle `θ₀` is periodic with the small-angle period: after
  each time `2π √(ℓ/g)` the motion returns to the angle `θ₀` with zero angular velocity. -/
lemma releasedFromRest_periodic (θ₀ : ℝ) :
    Function.Periodic (S.releasedFromRest θ₀) (S.smallAnglePeriod : Time) := by
  rw [S.releasedFromRest_eq θ₀]
  exact S.smallAngleTrajectory_periodic ⟨EuclideanSpace.single 0 θ₀, 0⟩

end SimplePendulum

end ClassicalMechanics

end
