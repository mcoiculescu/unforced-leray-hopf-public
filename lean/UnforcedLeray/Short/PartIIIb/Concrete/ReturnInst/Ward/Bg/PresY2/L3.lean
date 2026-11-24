import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Chart
import UnforcedLeray.Lib.AxisymmetricB.Average
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Rotation to the half-plane `φ = 0` (source 117-121, 2688-2689)

Proves `AzimuthRot`: every `z` is carried to `(ϱ(z), 0, z₃)` by a rotation about `e₃`.
The angle is the argument of `(z₀, z₁)`; the case of the axis needs no separate treatment.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem azimuthRot_proved : AzimuthRot := by
  intro z
  obtain ⟨θ, hc, hs⟩ : ∃ θ : ℝ, NearInst.hRad z * Real.cos θ = z 0 ∧
      NearInst.hRad z * Real.sin θ = z 1 := by
    have hw : ‖(⟨z 0, z 1⟩ : ℂ)‖ = NearInst.hRad z := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      rfl
    refine ⟨Complex.arg ⟨z 0, z 1⟩, ?_, ?_⟩
    · have h1 := Complex.norm_mul_cos_arg (⟨z 0, z 1⟩ : ℂ)
      rw [hw] at h1
      exact h1
    · have h1 := Complex.norm_mul_sin_arg (⟨z 0, z 1⟩ : ℂ)
      rw [hw] at h1
      exact h1
  refine ⟨rotZ (-θ), fixesAxis_rotZ (-θ), ?_⟩
  ext i
  fin_cases i
  · show Real.cos (-θ) * z 0 - Real.sin (-θ) * z 1 = NearInst.hRad z
    rw [Real.cos_neg, Real.sin_neg]
    linear_combination (-Real.cos θ) * hc + (-Real.sin θ) * hs
      + NearInst.hRad z * Real.cos_sq_add_sin_sq θ
  · show Real.sin (-θ) * z 0 + Real.cos (-θ) * z 1 = 0
    rw [Real.cos_neg, Real.sin_neg]
    linear_combination Real.sin θ * hc - Real.cos θ * hs
  · rfl

end UnforcedLeray.Short.PartIIIb.Concrete
