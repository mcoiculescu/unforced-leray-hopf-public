import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14
import UnforcedLeray.Infra.VolterraEvolution.Beta

/-!


For `s ≤ r < σ ≤ s + L`: `σ - r ≤ L`, so `1 ≤ √L (σ-r)^{-1/2}` and
`(1 + (σ-r)^{-1/2}) (r-s)^α ≤ (1 + √L) (σ-r)^{-1/2} (r-s)^α` with `α = n/2`.
Then the Beta integral `integral_kernel_mul_rpow` gives the closed form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- **`PartII-b:T22/1/14/6`**: the Beta-function step for the Volterra kernel. -/
theorem volterraStepBound_proof : UnforcedLeray.Short.IIb.CylPDE.VolterraStepBound := by
  intro s L σ n hL hsσ hσL
  set α : ℝ := (n : ℝ) / 2 with hαdef
  have hα0 : 0 ≤ α := by positivity
  have hαgt : -(1 / 2 : ℝ) < α := by linarith
  have hK : IntervalIntegrable (fun r : ℝ => (σ - r) ^ (-(1 / 2 : ℝ))) MeasureTheory.volume s σ :=
    UnforcedLeray.Infra.VolterraEvolution.intervalIntegrable_kernel σ s σ
  have hc : Continuous (fun r : ℝ => (r - s) ^ α) :=
    (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr hα0)
  have hf : IntervalIntegrable (fun r : ℝ => (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (r - s) ^ α)
      MeasureTheory.volume s σ := by
    have h1 : IntervalIntegrable (fun r : ℝ => (1 : ℝ) + (σ - r) ^ (-(1 / 2 : ℝ)))
        MeasureTheory.volume s σ :=
      intervalIntegrable_const.add hK
    exact h1.mul_continuousOn hc.continuousOn
  have hg : IntervalIntegrable (fun r : ℝ => (1 + Real.sqrt L) *
      ((σ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ α)) MeasureTheory.volume s σ :=
    (hK.mul_continuousOn hc.continuousOn).const_mul _
  have hle : ∀ r ∈ Ioo s σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (r - s) ^ α ≤
      (1 + Real.sqrt L) * ((σ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ α) := by
    intro r hr
    have hpos : 0 < σ - r := by linarith [hr.2]
    have hrL : σ - r ≤ L := by linarith [hr.1]
    have hkey : (σ - r) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (σ - r))⁻¹ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hpos.le]
    have hsp : 0 < Real.sqrt (σ - r) := Real.sqrt_pos.2 hpos
    have h1 : 1 ≤ Real.sqrt L * (σ - r) ^ (-(1 / 2 : ℝ)) := by
      rw [hkey, ← div_eq_mul_inv, le_div_iff₀ hsp]
      have := Real.sqrt_le_sqrt hrL
      linarith
    have hp : 0 ≤ (r - s) ^ α := Real.rpow_nonneg (by linarith [hr.1]) _
    have h2 := mul_le_mul_of_nonneg_right h1 hp
    nlinarith [h2]
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hsσ hf hg hle
  rw [intervalIntegral.integral_const_mul] at hmono
  have hbeta := UnforcedLeray.Infra.VolterraEvolution.integral_kernel_mul_rpow hsσ hαgt
  rw [hbeta] at hmono
  have e1 : α + 1 / 2 = ((n : ℝ) + 1) / 2 := by rw [hαdef]; ring
  have e2 : α + 1 + 1 / 2 = ((n : ℝ) + 1) / 2 + 1 := by rw [hαdef]; ring
  rw [e1, e2] at hmono
  refine hmono.trans (le_of_eq ?_)
  ring

end CylPDE

end UnforcedLeray.Short.IIb
