import UnforcedLeray.Short.Spine.Params
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Proof of `ParameterAsymptotics` (Spine, task A)

Source: `the November 2 reference manuscript`, lines 5945-5985: `ν_n ↓ 0` is the
phase-locked sequence, `ε_n³ = e^{-γ/ν_n}ν_n^{Re κ - 5 - 2σ₀}/(2|𝒞(σ₀)|)`, so that
`-ν_n log ε_n = γ/3 - (κ'/3) ν_n log ν_n + (log(2|𝒞(σ₀)|)/3) ν_n → γ/3`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

/-- The real-analysis core: `-ν log((e^{-γ/ν}ν^{κ'}/K)^{1/3}) → γ/3` as `ν → 0⁺`. -/
theorem tendsto_loss_aux (γ κ' K : ℝ) (hK : 0 < K) (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n)
    (hlim : Tendsto ν atTop (𝓝 0)) :
    Tendsto (fun n => -(ν n) * Real.log ((Real.exp (-(γ / ν n)) * ν n ^ κ' / K) ^ (1 / 3 : ℝ)))
      atTop (𝓝 (γ / 3)) := by
  have hml : Tendsto (fun n => ν n * Real.log (ν n)) atTop (𝓝 0) := by
    have h := (Real.continuous_mul_log.tendsto 0).comp hlim
    simpa [Function.comp_def] using h
  have key : ∀ n, -(ν n) * Real.log ((Real.exp (-(γ / ν n)) * ν n ^ κ' / K) ^ (1 / 3 : ℝ))
      = γ / 3 - (κ' / 3) * (ν n * Real.log (ν n)) + (Real.log K / 3) * ν n := by
    intro n
    have h0 : 0 < ν n := hν n
    have hpos : 0 < Real.exp (-(γ / ν n)) * ν n ^ κ' / K := by positivity
    rw [Real.log_rpow hpos, Real.log_div (by positivity) hK.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow h0]
    field_simp
    ring
  have h2 : Tendsto
      (fun n => γ / 3 - (κ' / 3) * (ν n * Real.log (ν n)) + (Real.log K / 3) * ν n) atTop
      (𝓝 (γ / 3 - (κ' / 3) * 0 + (Real.log K / 3) * 0)) :=
    (tendsto_const_nhds.sub (hml.const_mul _)).add (hlim.const_mul _)
  simp only [mul_zero, sub_zero, add_zero] at h2
  exact h2.congr (fun n => (key n).symm)

/-- `ParameterAsymptotics`: `ν_n > 0`, `ν_n → 0`, `ε_n > 0`, `-ν_n log ε_n → γ/3`. -/
theorem parameterAsymptotics : ParameterAsymptotics := by
  intro R hRc
  have h2 : StepPhaseLocked R.base :=
    ConstructionData.stepPhaseLocked_withPhaseLocked_of_C1 (F := R.seed) hRc
  obtain ⟨hpos, hlim, -⟩ := h2
  refine ⟨hpos, hlim, fun n => ConstructionData.amplitude_pos (F := R.base) hRc (hpos n), ?_⟩
  have hC : 0 < 2 * ‖R.base.C₀‖ := by
    have : R.base.C₀ ≠ 0 := hRc.2.2.2.1
    positivity
  exact tendsto_loss_aux R.base.growth (R.base.κ.re - 5 - 2 * R.base.σ₀) (2 * ‖R.base.C₀‖) hC
    R.base.ν hpos hlim

end UnforcedLeray.Short.Spine
