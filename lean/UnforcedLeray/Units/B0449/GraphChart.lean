import UnforcedLeray.Units.B0449.Chart
import UnforcedLeray.Units.B0447.Chart

/-!
# B0449 graph identity for the jointly measurable chart

The B0447 slice Laplacian identity is transferred from the canonical Lq slice to the jointly
measurable representative `chartJ`. This is the slice-level input for a space-time distributional
identity with non-product tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The B0447 spatial chart Laplacian identity holds for the jointly measurable representatives
`chartJ` and almost every time. -/
theorem chartJ_laplacian {ν : ℝ} (hν : 0 < ν) (hq1 : 1 < q)
    {w a : Yq P q} (h : HasPhaseOp (nuLapT ν) w a) (τ₀ : ℝ) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ e : CVec3,
        ∫ z, Heat.laplacian ψ z • dotL e (chartJ w ν τ₀ (t, z)) =
          (Real.exp (-t) : ℂ) * ∫ z, ψ z • dotL e (chartJ a ν τ₀ (t, z)) := by
  filter_upwards [B0447.chart_laplacian hν hq1 h τ₀ 0] with t ht
  intro ψ hψ hψc e
  have hw : (fun z => Heat.laplacian ψ z • dotL e (chartJ w ν τ₀ (t, z))) =ᵐ[volume]
      (fun z => Heat.laplacian ψ z • dotL e (chartPullback w ν τ₀ 0 t z)) := by
    filter_upwards [chartJ_slice hν w τ₀ t] with z hz
    rw [hz]
  have ha : (fun z => ψ z • dotL e (chartJ a ν τ₀ (t, z))) =ᵐ[volume]
      (fun z => ψ z • dotL e (chartPullback a ν τ₀ 0 t z)) := by
    filter_upwards [chartJ_slice hν a τ₀ t] with z hz
    rw [hz]
  have hwi : ∫ z, Heat.laplacian ψ z • dotL e (chartJ w ν τ₀ (t, z)) =
      ∫ z, Heat.laplacian ψ z • dotL e (chartPullback w ν τ₀ 0 t z) :=
    integral_congr_ae hw
  have hai : ∫ z, ψ z • dotL e (chartJ a ν τ₀ (t, z)) =
      ∫ z, ψ z • dotL e (chartPullback a ν τ₀ 0 t z) := integral_congr_ae ha
  calc
    ∫ z, Heat.laplacian ψ z • dotL e (chartJ w ν τ₀ (t, z)) =
        ∫ z, Heat.laplacian ψ z • dotL e (chartPullback w ν τ₀ 0 t z) := hwi
    _ = (Real.exp (-t) : ℂ) *
        ∫ z, ψ z • dotL e (chartPullback a ν τ₀ 0 t z) := ht ψ hψ hψc e
    _ = (Real.exp (-t) : ℂ) *
        ∫ z, ψ z • dotL e (chartJ a ν τ₀ (t, z)) := by rw [hai]

end UnforcedLeray.B0449
