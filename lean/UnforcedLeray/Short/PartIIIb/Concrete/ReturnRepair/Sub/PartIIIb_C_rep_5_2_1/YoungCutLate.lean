import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org

/-!
# `PartIII-b:C/rep/5/2/1/6`: late output gain (source 5317-5318)

On the support of `1 - χ_y(νs)` one has `4/5 < νs`, so `g⁻¹ ≤ e^{-4γ/(9ν)}` there
(`ftGain_late`).  Since `v - χ_y v = (1 - χ_y) v` a.e. (`youngMul_ae`) and `|1 - χ_y| ≤ 1`, the
pointwise bound `ginv² ‖(1-χ_y)v‖² ≤ e^{-8γ/(9ν)} ‖v‖²` integrates against `π ageμ` to the claim.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Real pointwise bound: `π' g² h² ≤ π' K² x²` when `0 ≤ h ≤ x` and `g ≤ K` whenever `h ≠ 0`. -/
theorem youngCutLate_real (π' g K h x : ℝ) (hπ : 0 ≤ π') (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hhx : h ≤ x) (hcase : h ≠ 0 → g ≤ K) :
    π' * g ^ 2 * h ^ 2 ≤ π' * (K ^ 2 * x ^ 2) := by
  by_cases h0 : h = 0
  · subst h0
    have h00 : π' * g ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
    rw [h00]
    exact mul_nonneg hπ (by positivity)
  · have hgK : g ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hg (hcase h0) 2
    have hhx2 : h ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hh hhx 2
    have hpt := mul_le_mul hgK hhx2 (sq_nonneg _) (sq_nonneg _)
    calc π' * g ^ 2 * h ^ 2 = π' * (g ^ 2 * h ^ 2) := by ring
      _ ≤ π' * (K ^ 2 * x ^ 2) := mul_le_mul_of_nonneg_left hpt hπ

theorem youngCutLate : YoungCutLate := by
  intro χ hχ c γ ν hγ hν v
  have hK0 : (0 : ℝ) ≤ Real.exp (-(4 * γ / 9) / ν) := (Real.exp_pos _).le
  have hcut : Measurable (cutFun χ ν) := cutFun_measurable_y hχ ν
  have hv : Measurable (v : Chart → Merid) := (Lp.stronglyMeasurable v).measurable
  have hae : ((v - youngMul hχ v : VelG c γ ν) : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
      fun p => (1 - cutFun χ ν p) • (v : Chart → Merid) p := by
    filter_upwards [Lp.coeFn_sub v (youngMul hχ v), youngMul_ae hχ v] with p hp1 hp2
    rw [hp1, Pi.sub_apply, hp2, sub_smul, one_smul]
  have hnorm : ENNReal.ofReal ‖v - youngMul hχ v‖ =
      eLpNorm (fun p => (1 - cutFun χ ν p) • (v : Chart → Merid) p) 2 (bodyMeasure c γ ν) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp (v - youngMul hχ v)).eLpNorm_lt_top.ne]
    exact eLpNorm_congr_ae hae
  rw [hnorm]
  have hE : ∀ (f : Chart → Merid) (μ : Measure Chart),
      eLpNorm f 2 μ ^ 2 = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ := by
    intro f μ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hHm : Measurable fun p : Chart => ‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ₑ ^ (2 : ℝ) :=
    ((measurable_const.sub hcut).smul hv).enorm.pow_const _
  have hgm : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) :=
    (((NearInst.ginv_measurable' γ ν).pow_const 2).const_mul Real.pi).ennreal_ofReal
  have hLb : ∫⁻ p, ‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν =
      ∫⁻ p, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) *
        ‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
    lintegral_withDensity_eq_lintegral_mul _ hgm hHm
  have hLs : ∀ f : Chart → ℝ≥0∞, ∫⁻ p, f p ∂srcMeasure c =
      ENNReal.ofReal Real.pi * ∫⁻ p, f p ∂ageμ c (-3 / 2) := by
    intro f
    unfold srcMeasure
    simp [lintegral_smul_measure]
  have hsq : eLpNorm (fun p => (1 - cutFun χ ν p) • (v : Chart → Merid) p) 2
        (bodyMeasure c γ ν) ^ 2 ≤
      (ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν)) *
        eLpNorm (v : Chart → Merid) 2 (srcMeasure c)) ^ 2 := by
    rw [hE, mul_pow, hE, hLb, hLs, ← ENNReal.ofReal_pow hK0]
    calc ∫⁻ p, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) *
            ‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)
        ≤ ∫⁻ p, ENNReal.ofReal Real.pi *
            (ENNReal.ofReal ((Real.exp (-(4 * γ / 9) / ν)) ^ 2) *
              ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)) ∂ageμ c (-3 / 2) := by
          refine lintegral_mono fun p => ?_
          dsimp only
          by_cases ht : 1 - cutFun χ ν p = 0
          · rw [show (1 - cutFun χ ν p) • (v : Chart → Merid) p = 0 by rw [ht, zero_smul],
              enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
            positivity
          · have hcut1 : cutFun χ ν p ≠ 1 := fun h => ht (by rw [h, sub_self])
            have hcut1' : χ (ν * p.1) ≠ 1 := hcut1
            have hgt : 4 / 5 < ν * p.1 := by
              by_contra hh
              push_neg at hh
              exact hcut1' (hχ.one _ hh)
            have hs : 4 / 5 / ν ≤ p.1 := by
              rw [div_le_iff₀ hν]
              linarith [mul_comm ν p.1]
            have hginv : ginv γ ν p ≤ Real.exp (-(4 * γ / 9) / ν) :=
              ftGain_late hγ hν (le_max_of_le_left hs)
            have hg0 : 0 ≤ ginv γ ν p := by
              unfold ginv UnforcedLeray.Short.IIIa.gainG
              positivity
            have hr : 0 ≤ cutFun χ ν p ∧ cutFun χ ν p ≤ 1 := hχ.range _
            have ht1 : ‖1 - cutFun χ ν p‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_le]
              constructor <;> linarith [hr.1, hr.2]
            have hHle : ‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ ≤
                ‖(v : Chart → Merid) p‖ := by
              rw [norm_smul]
              exact mul_le_of_le_one_left (norm_nonneg _) ht1
            have e1 : ‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ₑ ^ (2 : ℝ) =
                ENNReal.ofReal (‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖ ^ 2) := by
              rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
            have e2 : ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) =
                ENNReal.ofReal (‖(v : Chart → Merid) p‖ ^ 2) := by
              rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
            have e3 : ENNReal.ofReal Real.pi *
                (ENNReal.ofReal ((Real.exp (-(4 * γ / 9) / ν)) ^ 2) *
                  ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)) =
                ENNReal.ofReal (Real.pi * ((Real.exp (-(4 * γ / 9) / ν)) ^ 2 *
                  ‖(v : Chart → Merid) p‖ ^ 2)) := by
              rw [e2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul Real.pi_pos.le]
            have hgr := youngCutLate_real Real.pi (ginv γ ν p) (Real.exp (-(4 * γ / 9) / ν))
              (‖(1 - cutFun χ ν p) • (v : Chart → Merid) p‖) (‖(v : Chart → Merid) p‖)
              Real.pi_pos.le hg0 (norm_nonneg _) hHle (fun _ => hginv)
            rw [e1, e3, ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hgr
        _ = ENNReal.ofReal ((Real.exp (-(4 * γ / 9) / ν)) ^ 2) *
              (ENNReal.ofReal Real.pi * ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

end UnforcedLeray.Short.PartIIIb.Concrete
