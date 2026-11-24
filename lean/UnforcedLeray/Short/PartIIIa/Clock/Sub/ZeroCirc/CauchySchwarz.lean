import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves

namespace UnforcedLeray.Short.IIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- The `L²` norm of a square-integrable function, written through its integral of `‖f‖²`. -/
lemma zc_eLpNorm_two_toReal {α : Type*} {mα : MeasurableSpace α} {ν : Measure α} {E : Type*}
    [NormedAddCommGroup E] {f : α → E} (hf : MemLp f 2 ν) :
    (eLpNorm f 2 ν).toReal = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [ENNReal.toReal_ofReal]
  exact Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _

theorem zcCauchySchwarz : UnforcedLeray.Short.IIIa.ZCCauchySchwarz := by
  unfold UnforcedLeray.Short.IIIa.ZCCauchySchwarz
  intro μ a g ha hg
  have ha' : MemLp (fun x => ‖a x‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact ha.norm
  have hg' : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact hg.norm
  calc ‖∫ x, a x * (g x : ℂ) ∂μ‖
      ≤ ∫ x, ‖a x * (g x : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖a x‖ * ‖g x‖ ∂μ := by
      simp only [norm_mul, Complex.norm_real]
    _ = ∫ x, ‖‖a x‖‖ * ‖‖g x‖‖ ∂μ := by
      simp only [norm_norm]
    _ ≤ (∫ x, ‖‖a x‖‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ x, ‖‖g x‖‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two ha' hg'
    _ = (eLpNorm a 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
      simp only [norm_norm]
      rw [zc_eLpNorm_two_toReal ha, zc_eLpNorm_two_toReal hg]

end UnforcedLeray.Short.IIIa
