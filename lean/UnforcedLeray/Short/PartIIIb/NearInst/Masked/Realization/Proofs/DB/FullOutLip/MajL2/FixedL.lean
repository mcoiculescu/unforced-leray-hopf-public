import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.YoungDilated
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PeriodShift

/-!
# Fixed dilation `l` for the radial dilated kernel `fmKer` (source 4001-4003)

Copy of the proof of `dilMajFixedL_of` with the kernel `farKern d` replaced by `fmKer ν l`
(measurable in `w` for fixed `l ∈ (0,1)`). Young's inequality `youngDilated_holds` at each phase
`τ`, then the removal of the shift `σ = 2 log l` by `periodShift_holds`, gives the weight
`l^{2μ+2} l^{-3/2} = l^{2μ+1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`. -/
private lemma fmfl_sq_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- `(x^2)^{1/2} = x` in `ℝ≥0∞`. -/
private lemma fmfl_sqrt_sq (x : ℝ≥0∞) : (x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

theorem fmFixedL : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmFixedL := by
  intro ν μ g hg P hP0 hper A l hl hA
  have hl0 : 0 < l := hl.1
  have hfk : ∀ w : UnforcedLeray.Space, fmKer ν l w =
      ENNReal.ofReal ((ν * (1 - l ^ 2)) ^ (-2 : ℝ) *
        (1 + ‖w‖ / Real.sqrt (ν * (1 - l ^ 2))) ^ (-4 : ℝ)) := by
    intro w
    unfold fmKer
    rw [if_pos hl]
  have hfmK : Measurable (fun w : UnforcedLeray.Space => fmKer ν l w) := by
    simp_rw [hfk]
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  -- the source profile at shifted phase is measurable in `z`
  have hG : ∀ τ : ℝ, Measurable (fun z : UnforcedLeray.Space => g (τ + 2 * Real.log l) z) :=
    fun τ => hg.comp (measurable_const.prodMk measurable_id)
  -- the fixed-phase `L²_z` mass is measurable in `τ`
  have hH : Measurable (fun τ : ℝ => ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) := by
    have hf2 : Measurable (fun p : ℝ × UnforcedLeray.Space => Function.uncurry g p ^ (2 : ℝ)) :=
      hg.pow_const _
    exact hf2.lintegral_prod_right'
  have hG2 : Measurable (fun τ : ℝ => ∫⁻ z : UnforcedLeray.Space,
      g (τ + 2 * Real.log l) z ^ (2 : ℝ)) :=
    hH.comp (measurable_id.add_const _)
  -- periodicity of the `L²_z` mass, and the removal of the shift
  have hHper : ∀ τ : ℝ, (∫⁻ z : UnforcedLeray.Space, g (τ + P) z ^ (2 : ℝ)) =
      ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ) := fun τ => by
    simp only [hper]
  have hPS : ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)
      = ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ) := by
    have := periodShift_holds (fun τ : ℝ => ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) P 0
      (2 * Real.log l) hP0 hH hHper
    rw [zero_add] at this
    exact this
  -- the pointwise-in-`τ` bound by Young
  have hpt : ∀ τ : ℝ,
      ∫⁻ y : UnforcedLeray.Space,
          (ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
            ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
              ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)) := by
    intro τ
    have hYb := youngDilated_holds (fmKer ν l) (fun z => g (τ + 2 * Real.log l) z) hfmK (hG τ)
      A hA l hl0
    have hX : ∫⁻ y : UnforcedLeray.Space,
        (∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
            ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ) := by
      have h := ENNReal.rpow_le_rpow hYb (by norm_num : (0 : ℝ) ≤ 2)
      rw [fmfl_sq_half, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        fmfl_sq_half] at h
      exact h
    have hc2 : ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have e : ∀ y : UnforcedLeray.Space,
        (ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
        = ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
          (∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ) :=
      fun y => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    rw [lintegral_congr e, lintegral_const_mul' _ _ hc2]
    gcongr
  have hT : ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
          (ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
      ≤ ∫⁻ τ in Ico (0 : ℝ) P, ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
            ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
              ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)) :=
    lintegral_mono (fun τ => hpt τ)
  have hmeas : Measurable (fun τ : ℝ => (ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
      ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)) :=
    measurable_const.mul hG2
  have hcK : ENNReal.ofReal (l ^ (2 * μ + 2)) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) =
      ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl0.le _), ← Real.rpow_add hl0]
    congr 2
    ring
  calc (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
          (ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ τ in Ico (0 : ℝ) P, ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
            ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
              ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hT (by norm_num)
    _ = (ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
          ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
            ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ))) ^ (1 / 2 : ℝ) := by
        congr 1
        rw [lintegral_const_mul _ hmeas, lintegral_const_mul _ hG2, hPS]
    _ = ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          fmfl_sqrt_sq, fmfl_sqrt_sq]
    _ = ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← hcK]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
