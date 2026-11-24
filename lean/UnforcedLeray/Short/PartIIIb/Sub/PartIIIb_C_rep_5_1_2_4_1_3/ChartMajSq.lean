import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/1`: the chart majorant squared

Source `the November 2 reference manuscript` 2683 (`𝒩_T g = s g`), 3611-3621,
5588.  Proves `ChartMajSq`:
`wardYChartMaj(p)² ≤ ofReal(p.1⁻¹) · psiMaj(chartTau p, chartY p)²`.

Step 1: `wardYKerMaj ≤ psiMaj` pointwise in the source, using `cartLiftFrobBound`
(`srcNorm (oldPhys g) σ z ≤ age z · ‖g(chartOf z σ)‖ₑ = srcW σ z`).
Step 2: `(√s)⁻¹² ≤ s⁻¹` (equality for `s ≥ 0`; for `s < 0` the left side is zero).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

theorem chartMajSq : ChartMajSq := by
  intro R c θ g p
  -- Step 2 (scalar): `ofReal((√s)⁻¹)^2 ≤ ofReal(s⁻¹)`
  have hsq : ∀ s : ℝ, ENNReal.ofReal ((Real.sqrt s)⁻¹) ^ (2 : ℝ) ≤ ENNReal.ofReal s⁻¹ := by
    intro s
    have hx : 0 ≤ (Real.sqrt s)⁻¹ := by positivity
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hx]
    rcases le_or_gt 0 s with hs | hs
    · apply ENNReal.ofReal_le_ofReal
      rw [inv_pow, Real.sq_sqrt hs]
    · rw [Real.sqrt_eq_zero'.mpr hs.le, inv_zero]
      simp
  -- Step 1 (pointwise): `srcNorm (oldPhys g) σ z ≤ srcW σ z`
  have hpt : ∀ σ z, UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) σ z ≤
      srcW R c (fun q => ‖g q‖ₑ) σ z := by
    intro σ z
    show ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (oldPhys R c g σ z)) ≤
      ENNReal.ofReal (age R z) * ‖g (NearInst.chartOf R c z σ)‖ₑ
    have hage : 0 ≤ age R z := by unfold age; positivity
    have he : ‖g (NearInst.chartOf R c z σ)‖ₑ = ENNReal.ofReal ‖g (NearInst.chartOf R c z σ)‖ := by
      first
        | exact (ofReal_norm' _).symm
        | simp [ofReal_norm', enorm_eq_nnnorm]
        | rfl
    rw [he, ← ENNReal.ofReal_mul hage]
    apply ENNReal.ofReal_le_ofReal
    exact cartLiftFrobBound R c g σ z
  -- Step 1 (integrated): `wardYKerMaj ≤ psiMaj`
  have hA : ∀ (τ : ℝ) (y : Space), wardYKerMaj R c θ g τ y ≤
      psiMaj R c θ (fun q => ‖g q‖ₑ) τ y := by
    intro τ y
    unfold wardYKerMaj psiMaj
    exact lintegral_mono fun l => lintegral_mono fun z =>
      mul_le_mul' le_rfl (hpt _ _)
  -- Assemble
  unfold wardYChartMaj
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul' (hsq p.1)
    (ENNReal.rpow_le_rpow (hA (NearInst.chartTau R p) (NearInst.chartY R p)) (by norm_num))

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
