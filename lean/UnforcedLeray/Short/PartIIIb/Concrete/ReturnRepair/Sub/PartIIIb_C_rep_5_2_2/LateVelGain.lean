import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg

/-!
# `PartIII-b:C/rep/5/2/2/4`: late output gain (source 5317-5318)

On the set where `F ≠ 0` and `0 < s` one has `ν s ≥ 4/5`, hence `g⁻¹ ≤ e^{-4γ/(9ν)}`
(`ftGain_late`). The gain norm of `v` is the `L²` norm for `bodyMeasure = ageμ.withDensity (π g⁻²)`;
since `v = F` `bodyMeasure`-a.e. and the density is bounded by `e^{-8γ/(9ν)} π` on the support of
`F`, the squared norm is bounded by `e^{-8γ/(9ν)}` times the squared ungained norm.

The lower-bound direction is `lintegral_withDensity_le_lintegral_mul`, which needs no
measurability of `F`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Real pointwise bound: `π' g² x² ≤ K² (π' x²)` when `0 ≤ g` and `g ≤ K` whenever `x ≠ 0`. -/
theorem lateVelGain_real (π' g K x : ℝ) (hπ : 0 ≤ π') (hg : 0 ≤ g)
    (hcase : x ≠ 0 → g ≤ K) : π' * g ^ 2 * x ^ 2 ≤ K ^ 2 * (π' * x ^ 2) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hgK : g ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hg (hcase hx0) 2
    calc π' * g ^ 2 * x ^ 2 = π' * (g ^ 2 * x ^ 2) := by ring
      _ ≤ π' * (K ^ 2 * x ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgK (sq_nonneg x)) hπ
      _ = K ^ 2 * (π' * x ^ 2) := by ring

theorem lateVelGain : LateVelGain := by
  intro c γ ν hγ hν v F hvF hF0
  have hK0 : (0 : ℝ) ≤ Real.exp (-(4 * γ / 9) / ν) := (Real.exp_pos _).le
  have hfm : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) :=
    (((NearInst.ginv_measurable' γ ν).pow_const 2).const_mul Real.pi).ennreal_ofReal
  have hpos : ∀ᵐ p ∂(ageμ c (-3 / 2)), 0 < p.1 := by
    have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))), 0 < s :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
    unfold ageμ
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hE : ∀ (f : Chart → Merid) (μ : Measure Chart),
      eLpNorm f 2 μ ^ 2 = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ := by
    intro f μ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hLs : ∀ f : Chart → ℝ≥0∞, ∫⁻ p, f p ∂srcMeasure c =
      ENNReal.ofReal Real.pi * ∫⁻ p, f p ∂ageμ c (-3 / 2) := by
    intro f
    unfold srcMeasure
    simp [lintegral_smul_measure]
  have hnorm : ENNReal.ofReal ‖v‖ = eLpNorm (v : Chart → Merid) 2 (bodyMeasure c γ ν) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp v).eLpNorm_lt_top.ne]
  rw [hnorm, eLpNorm_congr_ae hvF]
  have hsq : eLpNorm F 2 (bodyMeasure c γ ν) ^ 2 ≤
      (ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν)) * eLpNorm F 2 (srcMeasure c)) ^ 2 := by
    have hR : (ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν)) * eLpNorm F 2 (srcMeasure c)) ^ 2 =
        ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2) *
          (ENNReal.ofReal Real.pi * ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)) := by
      rw [mul_pow, hE F (srcMeasure c), hLs, ← ENNReal.ofReal_pow hK0]
    rw [hE F, hR]
    unfold bodyMeasure
    refine (lintegral_withDensity_le_lintegral_mul _ hfm _).trans ?_
    calc _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2) *
            (ENNReal.ofReal Real.pi * ‖F p‖ₑ ^ (2 : ℝ)) ∂ageμ c (-3 / 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpos] with p hp
          show ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖F p‖ₑ ^ (2 : ℝ) ≤
            ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2) *
              (ENNReal.ofReal Real.pi * ‖F p‖ₑ ^ (2 : ℝ))
          have e2 : ‖F p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖F p‖ ^ 2) := by
            rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
          rw [e2]
          have hgle : ‖F p‖ ≠ 0 → ginv γ ν p ≤ Real.exp (-(4 * γ / 9) / ν) := by
            intro hx
            have hFp : F p ≠ 0 := fun h => hx (by rw [h, norm_zero])
            have hs : 4 / 5 ≤ ν * p.1 := by
              by_contra hh
              exact hFp (hF0 p hp (not_le.mp hh))
            have hs' : 4 / 5 / ν ≤ p.1 := by
              rw [div_le_iff₀ hν]
              linarith [mul_comm ν p.1]
            exact ftGain_late hγ hν (le_max_of_le_left hs')
          have hg0 : 0 ≤ ginv γ ν p := by
            unfold ginv UnforcedLeray.Short.IIIa.gainG
            positivity
          have hreal := lateVelGain_real Real.pi (ginv γ ν p) (Real.exp (-(4 * γ / 9) / ν))
            ‖F p‖ Real.pi_pos.le hg0 hgle
          calc ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ENNReal.ofReal (‖F p‖ ^ 2)
              = ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2 * ‖F p‖ ^ 2) :=
                (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.pi * ginv γ ν p ^ 2)).symm
            _ ≤ ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2 * (Real.pi * ‖F p‖ ^ 2)) :=
                ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2) *
                ENNReal.ofReal (Real.pi * ‖F p‖ ^ 2) :=
                ENNReal.ofReal_mul (sq_nonneg _)
            _ = ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2) *
                (ENNReal.ofReal Real.pi * ENNReal.ofReal (‖F p‖ ^ 2)) := by
                rw [ENNReal.ofReal_mul Real.pi_pos.le]
      _ = ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν) ^ 2) *
            (ENNReal.ofReal Real.pi * ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

end UnforcedLeray.Short.PartIIIb.Concrete
