import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Fixed dilation `l` for the dilated positive kernel (source 4001-4003)

For fixed `l > 0`, Young's inequality `YoungDilated` at each phase `τ` gives an `L²_y` bound
`l^{-3/2} A ‖g(τ+σ,·)‖_{L²_z}` with `σ = 2 log l`. Multiplying by `l^{2μ+2}`, squaring, integrating
over `τ ∈ [0,P)` and removing the shift `σ` by `PeriodShift` (the `P`-periodic profile
`τ ↦ ∫ g(τ,z)² dz`) gives the bound with the weight `l^{2μ+2} l^{-3/2} = l^{2μ+1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`. -/
private lemma dfl_sq_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- `(x^2)^{1/2} = x` in `ℝ≥0∞`. -/
private lemma dfl_sqrt_sq (x : ℝ≥0∞) : (x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

theorem dilMajFixedL_of (hY : YoungDilated) (hP : PeriodShift) (hM : DilMajMeasurable) :
    DilMajFixedL := by
  intro μ d g hg P hP0 hper A hA l hl
  have hfar : Measurable (farKern d) := by
    unfold farKern
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) measurable_const
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
    have := hP (fun τ : ℝ => ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) P 0
      (2 * Real.log l) hP0 hH hHper
    rw [zero_add] at this
    exact this
  -- the pointwise-in-`τ` bound by Young
  have hpt : ∀ τ : ℝ,
      ∫⁻ y : UnforcedLeray.Space,
          (ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
            ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
              ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)) := by
    intro τ
    have hYb := hY (farKern d) (fun z => g (τ + 2 * Real.log l) z) hfar (hG τ) A hA l hl
    have hX : ∫⁻ y : UnforcedLeray.Space,
        (∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
            ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ) := by
      have h := ENNReal.rpow_le_rpow hYb (by norm_num : (0 : ℝ) ≤ 2)
      rw [dfl_sq_half, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        dfl_sq_half] at h
      exact h
    have hc2 : ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have e : ∀ y : UnforcedLeray.Space,
        (ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
        = ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
          (∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ) :=
      fun y => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    rw [lintegral_congr e, lintegral_const_mul' _ _ hc2]
    gcongr
  have hT : ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
          (ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)
      ≤ ∫⁻ τ in Ico (0 : ℝ) P, ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
            ((ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
              ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)) :=
    lintegral_mono (fun τ => hpt τ)
  have hmeas : Measurable (fun τ : ℝ => (ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A) ^ (2 : ℝ) *
      ∫⁻ z : UnforcedLeray.Space, g (τ + 2 * Real.log l) z ^ (2 : ℝ)) :=
    measurable_const.mul hG2
  have hcK : ENNReal.ofReal (l ^ (2 * μ + 2)) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) =
      ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl.le _), ← Real.rpow_add hl]
    congr 2
    ring
  calc (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
          (ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
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
          dfl_sqrt_sq, dfl_sqrt_sq]
    _ = ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← hcK]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
