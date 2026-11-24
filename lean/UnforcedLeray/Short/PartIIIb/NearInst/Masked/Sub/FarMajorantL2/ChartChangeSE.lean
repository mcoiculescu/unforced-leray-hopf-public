import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Planar chart change of variables `(s, η) ↦ (ρ, t)` (source 2666-2668)

With `ρ = R/√s` and `t = η/√s`, `ρ dρ dt = (R²/2) s^{-5/2} ds dη`. The proof first integrates out
`t` (a dilation, `scale`), giving `∫ η ... = s^{-2} F(R/√s)` with `F ρ = ∫ t Ψ(ρ, t)`, and then
performs the one-variable substitution `ρ = R/√s` on `(0, ∞)` (`lintegral_image_eq_lintegral_abs_deriv_mul`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem chartChangeSE_holds : ChartChangeSE := by
  intro R lo hR hlo Ψ hΨ
  have hRne : R ≠ 0 := hR.ne'
  -- dilation in the second variable
  have scale : ∀ (a : ℝ), 0 < a → ∀ g : ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ η : ℝ, g (η / a) = ENNReal.ofReal a * ∫⁻ t : ℝ, g t := by
    intro a ha g hg
    have hm := Real.map_volume_mul_left (a := a⁻¹) (inv_ne_zero ha.ne')
    have h1 : ∫⁻ x, g x ∂(Measure.map (fun y : ℝ => a⁻¹ * y) volume)
        = ∫⁻ η : ℝ, g (a⁻¹ * η) :=
      lintegral_map hg (measurable_const_mul a⁻¹)
    rw [hm, inv_inv, abs_of_pos ha, lintegral_smul_measure] at h1
    simp only [div_eq_inv_mul]
    exact h1.symm
  -- the inner integral at fixed `s`
  have inner : ∀ s : ℝ, 0 < s →
      ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Ψ (R / √s) (η / √s)
        = ENNReal.ofReal (s ^ (-2 : ℝ)) * ∫⁻ t : ℝ, Ψ (R / √s) t := by
    intro s hs
    have hsqrt : 0 < √s := Real.sqrt_pos.2 hs
    have hmeas : Measurable (Ψ (R / √s)) := hΨ.comp (measurable_const.prodMk measurable_id)
    have e : s ^ (-5 / 2 : ℝ) * √s = s ^ (-2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
      norm_num
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, scale _ hsqrt _ hmeas, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), e]
  -- the chart set and its image under `s ↦ R/√s`
  have hS : MeasurableSet {s : ℝ | 0 < s ∧ lo < R / √s} :=
    measurableSet_Ioi.inter
      (measurableSet_lt measurable_const (measurable_const.div Real.continuous_sqrt.measurable))
  have himg : (fun s : ℝ => R / √s) '' {s : ℝ | 0 < s ∧ lo < R / √s} = Ioi lo := by
    ext ρ
    constructor
    · rintro ⟨s, ⟨_, hlo'⟩, rfl⟩
      exact hlo'
    · intro hρ
      have hρ' : lo < ρ := hρ
      have hρpos : 0 < ρ := lt_of_le_of_lt hlo hρ'
      have e : R / √((R / ρ) ^ 2) = ρ := by
        rw [Real.sqrt_sq (by positivity)]
        field_simp
      refine ⟨(R / ρ) ^ 2, ⟨by positivity, ?_⟩, e⟩
      rw [e]
      exact hρ'
  have hinj : Set.InjOn (fun s : ℝ => R / √s) {s : ℝ | 0 < s ∧ lo < R / √s} := by
    rintro a ⟨ha, _⟩ b ⟨hb, _⟩ hab
    have hab' : √a = √b := by
      have hA : 0 < √a := Real.sqrt_pos.2 ha
      have hB : 0 < √b := Real.sqrt_pos.2 hb
      have h : R / √a = R / √b := hab
      rw [div_eq_div_iff hA.ne' hB.ne'] at h
      exact (mul_left_cancel₀ hRne h).symm
    have h1 := Real.sq_sqrt ha.le
    have h2 := Real.sq_sqrt hb.le
    rw [← h1, ← h2, hab']
  have hderiv : ∀ s ∈ {s : ℝ | 0 < s ∧ lo < R / √s},
      HasDerivWithinAt (fun s : ℝ => R / √s) (-(R / (2 * √s * s)))
        {s : ℝ | 0 < s ∧ lo < R / √s} s := by
    rintro s ⟨hs, _⟩
    have hsq : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    have h := (hasDerivAt_const s R).div (Real.hasDerivAt_sqrt hs.ne') hsq
    have h2 : HasDerivAt (fun s : ℝ => R / √s) ((0 * √s - R * (1 / (2 * √s))) / √s ^ 2) s := h
    apply HasDerivAt.hasDerivWithinAt
    refine h2.congr_deriv ?_
    rw [Real.sq_sqrt hs.le]
    field_simp
    ring
  -- the algebraic identity on the chart set
  have key2 : ∀ x : ℝ, 0 < x →
      ENNReal.ofReal |-(R / (2 * √x * x))| * ENNReal.ofReal (R / √x)
        = ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal (x ^ (-2 : ℝ)) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ x = t ^ 2 :=
      ⟨√x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
    rw [Real.sqrt_sq ht.le]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ R ^ 2 / 2)]
    congr 1
    rw [abs_neg, abs_of_pos (by positivity), Real.rpow_neg (by positivity), Real.rpow_two]
    field_simp
  -- the change of variables
  have hcov : ∫⁻ ρ in (fun s : ℝ => R / √s) '' {s : ℝ | 0 < s ∧ lo < R / √s},
        ∫⁻ t : ℝ, ENNReal.ofReal ρ * Ψ ρ t
      = ∫⁻ x in {s : ℝ | 0 < s ∧ lo < R / √s},
          ENNReal.ofReal |-(R / (2 * √x * x))| * ∫⁻ t : ℝ, ENNReal.ofReal (R / √x) * Ψ (R / √x) t :=
    lintegral_image_eq_lintegral_abs_deriv_mul hS hderiv hinj _
  calc ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * Ψ ρ t
      = ∫⁻ ρ in (fun s : ℝ => R / √s) '' {s : ℝ | 0 < s ∧ lo < R / √s},
          ∫⁻ t : ℝ, ENNReal.ofReal ρ * Ψ ρ t := by rw [himg]
    _ = ∫⁻ x in {s : ℝ | 0 < s ∧ lo < R / √s},
          ENNReal.ofReal |-(R / (2 * √x * x))| * ∫⁻ t : ℝ, ENNReal.ofReal (R / √x) * Ψ (R / √x) t :=
        hcov
    _ = ∫⁻ x in {s : ℝ | 0 < s ∧ lo < R / √s}, ENNReal.ofReal (R ^ 2 / 2) *
          ∫⁻ η : ℝ, ENNReal.ofReal (x ^ (-5 / 2 : ℝ)) * Ψ (R / √x) (η / √x) := by
        refine setLIntegral_congr_fun hS ?_
        intro x hx
        dsimp only
        have hx0 : 0 < x := hx.1
        rw [inner x hx0, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [← mul_assoc, ← mul_assoc, key2 x hx0]
    _ = ENNReal.ofReal (R ^ 2 / 2) * ∫⁻ x in {s : ℝ | 0 < s ∧ lo < R / √s}, ∫⁻ η : ℝ,
          ENNReal.ofReal (x ^ (-5 / 2 : ℝ)) * Ψ (R / √x) (η / √x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
