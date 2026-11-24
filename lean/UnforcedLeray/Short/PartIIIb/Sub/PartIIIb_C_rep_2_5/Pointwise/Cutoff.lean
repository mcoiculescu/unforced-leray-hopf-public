import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Decay

/-!
# `PartIII-b:C/rep/2/5`, pointwise leaf: the stream cutoff profile (source 4164-4167, 4181-4192)

Bounds `|χ'| ≤ M₁`, `|χ''| ≤ M₂` of a stream cutoff, its values off the transition layer, and the
radial coefficient `G(r) = χ'(νR²/r²)(-2νR²/r³)/r` (the `f(ϱ) = χ_y'/ϱ` of the source) with
`|G| ≤ 2M₁ L⁻²`, `|G'| ≤ (4M₂+8M₁) L⁻³` for `r ≥ L`, `L² = νR²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wgx_bdd (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, t < 4 / 5 ∨ 1 < t → g t = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |g t| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (4 / 5 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (4 / 5 : ℝ) 1
  · have := hC t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have : t < 4 / 5 ∨ 1 < t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      exact ht
    rw [h0 t this]
    simpa using le_max_right C 0

theorem wgx_deriv_zero_lt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : t < 4 / 5) :
    deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
  have hev : ∀ᶠ s in nhds t, s < 4 / 5 := isOpen_Iio.mem_nhds ht
  have h1 : χ =ᶠ[nhds t] fun _ => (1 : ℝ) := hev.mono fun s hs => hχ.one s hs.le
  have h1' : deriv χ t = 0 := by rw [h1.deriv_eq]; simp
  refine ⟨h1', ?_⟩
  have h2 : deriv χ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with s hs
    have h1s : χ =ᶠ[nhds s] fun _ => (1 : ℝ) :=
      Filter.Eventually.mono (isOpen_Iio.mem_nhds (show s ∈ Iio (4 / 5 : ℝ) from hs))
        fun r hr => hχ.one r hr.le
    rw [h1s.deriv_eq]; simp
  rw [h2.deriv_eq]; simp

theorem wgx_deriv_zero_gt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : 1 < t) :
    deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
  have hev : ∀ᶠ s in nhds t, 1 < s := isOpen_Ioi.mem_nhds ht
  have h1 : χ =ᶠ[nhds t] fun _ => (0 : ℝ) := hev.mono fun s hs => hχ.zero s hs.le
  have h1' : deriv χ t = 0 := by rw [h1.deriv_eq]; simp
  refine ⟨h1', ?_⟩
  have h2 : deriv χ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with s hs
    have h1s : χ =ᶠ[nhds s] fun _ => (0 : ℝ) :=
      Filter.Eventually.mono (isOpen_Ioi.mem_nhds (show s ∈ Ioi (1 : ℝ) from hs))
        fun r hr => hχ.zero r hr.le
    rw [h1s.deriv_eq]; simp
  rw [h2.deriv_eq]; simp

theorem wgx_chi_smooth {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv χ) :=
  (show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χ from hχ.smooth).deriv'

theorem wgx_chi_bounds {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) :
    ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ (∀ t, |deriv χ t| ≤ M1) ∧
      (∀ t, |deriv (deriv χ) t| ≤ M2) := by
  have hd := wgx_chi_smooth hχ
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤)
  have hc1 : Continuous (deriv χ) := hd.continuous
  have hc2 : Continuous (deriv (deriv χ)) := hd.continuous_deriv hle
  obtain ⟨M1, h1, hb1⟩ := wgx_bdd _ hc1 (fun t ht => by
    rcases ht with ht | ht
    · exact (wgx_deriv_zero_lt hχ ht).1
    · exact (wgx_deriv_zero_gt hχ ht).1)
  obtain ⟨M2, h2, hb2⟩ := wgx_bdd _ hc2 (fun t ht => by
    rcases ht with ht | ht
    · exact (wgx_deriv_zero_lt hχ ht).2
    · exact (wgx_deriv_zero_gt hχ ht).2)
  exact ⟨M1, M2, h1, h2, hb1, hb2⟩

/-- The radial coefficient `G` and its derivative. -/
theorem wgx_G_deriv {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {M1 M2 : ℝ}
    (hM1 : ∀ t, |deriv χ t| ≤ M1) (hM2 : ∀ t, |deriv (deriv χ) t| ≤ M2)
    {ν R L : ℝ} (hν : 0 < ν) (hL : 0 < L) (hLsq : ν * R ^ 2 = L ^ 2) {ρ : ℝ} (hρ : L ≤ ρ) :
    ∃ G' : ℝ, HasDerivAt
        (fun r : ℝ => deriv χ (ν * (R ^ 2 / r ^ 2)) * (-2 * ν * R ^ 2 / r ^ 3) / r) G' ρ ∧
      |G'| ≤ (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hL hρ
  have hdiff : Differentiable ℝ (deriv χ) := by
    exact (wgx_chi_smooth hχ).differentiable (by simp)
  have h1 : HasDerivAt (fun r : ℝ => R ^ 2 / r ^ 2) (-(2 * R ^ 2 / ρ ^ 3)) ρ :=
    hasDerivAt_sq_div R hρ0.ne'
  have h2 := h1.const_mul ν
  have h3 : HasDerivAt (deriv χ) (deriv (deriv χ) (ν * (R ^ 2 / ρ ^ 2)))
      (ν * (R ^ 2 / ρ ^ 2)) := (hdiff _).hasDerivAt
  have hu := h3.comp ρ h2
  have hv : HasDerivAt (fun r : ℝ => -2 * ν * R ^ 2 / r ^ 3) (6 * ν * R ^ 2 / ρ ^ 4) ρ := by
    have := (hasDerivAt_const ρ (-2 * ν * R ^ 2)).div (hasDerivAt_pow 3 ρ)
      (pow_ne_zero 3 hρ0.ne')
    refine this.congr_deriv ?_
    field_simp
    ring
  have hw : HasDerivAt (fun r : ℝ => r) 1 ρ := hasDerivAt_id ρ
  have hG := (hu.mul hv).div hw hρ0.ne'
  refine ⟨_, hG, ?_⟩
  simp only [Function.comp_apply, Pi.mul_apply]
  set d1 := deriv χ (ν * (R ^ 2 / ρ ^ 2)) with hd1
  set d2 := deriv (deriv χ) (ν * (R ^ 2 / ρ ^ 2)) with hd2
  set p := ρ⁻¹ with hp
  have hp0 : 0 < p := inv_pos.2 hρ0
  have hpl : p ≤ L⁻¹ := inv_anti₀ hL hρ
  have hℓ : 0 < L⁻¹ := inv_pos.2 hL
  have hLℓ : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have hR2 : R ^ 2 = L ^ 2 / ν := eq_div_of_mul_eq hν.ne' (by rw [mul_comm]; exact hLsq)
  have hform : ((d2 * (ν * -(2 * R ^ 2 / ρ ^ 3)) * (-2 * ν * R ^ 2 / ρ ^ 3) +
        d1 * (6 * ν * R ^ 2 / ρ ^ 4)) * ρ - d1 * (-2 * ν * R ^ 2 / ρ ^ 3) * 1) / ρ ^ 2 =
      4 * d2 * L ^ 4 * p ^ 7 + 8 * d1 * L ^ 2 * p ^ 5 := by
    rw [hR2, hp]
    field_simp
    ring
  rw [hform]
  have hL3 : L ^ 4 * p ^ 7 ≤ (L⁻¹) ^ 3 := by
    calc L ^ 4 * p ^ 7 ≤ L ^ 4 * (L⁻¹) ^ 7 := by gcongr
      _ = (L⁻¹) ^ 3 := by field_simp
  have hL2 : L ^ 2 * p ^ 5 ≤ (L⁻¹) ^ 3 := by
    calc L ^ 2 * p ^ 5 ≤ L ^ 2 * (L⁻¹) ^ 5 := by gcongr
      _ = (L⁻¹) ^ 3 := by field_simp
  have hM1n : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2n : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  have e1 : |4 * d2 * L ^ 4 * p ^ 7| = 4 * |d2| * (L ^ 4 * p ^ 7) := by
    rw [show 4 * d2 * L ^ 4 * p ^ 7 = (4 * (L ^ 4 * p ^ 7)) * d2 by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    ring
  have e2 : |8 * d1 * L ^ 2 * p ^ 5| = 8 * |d1| * (L ^ 2 * p ^ 5) := by
    rw [show 8 * d1 * L ^ 2 * p ^ 5 = (8 * (L ^ 2 * p ^ 5)) * d1 by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    ring
  calc |4 * d2 * L ^ 4 * p ^ 7 + 8 * d1 * L ^ 2 * p ^ 5|
      ≤ |4 * d2 * L ^ 4 * p ^ 7| + |8 * d1 * L ^ 2 * p ^ 5| := abs_add_le _ _
    _ = 4 * |d2| * (L ^ 4 * p ^ 7) + 8 * |d1| * (L ^ 2 * p ^ 5) := by rw [e1, e2]
    _ ≤ 4 * M2 * (L⁻¹) ^ 3 + 8 * M1 * (L⁻¹) ^ 3 := by
        gcongr
        · exact hM2 _
        · exact hM1 _
    _ = (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 := by ring

/-- `|G(ρ)| ≤ 2 M₁ L⁻²` for `ρ ≥ L`. -/
theorem wgx_G_bound {χ : ℝ → ℝ} {M1 : ℝ} (hM1 : ∀ t, |deriv χ t| ≤ M1)
    {ν R L : ℝ} (hν : 0 < ν) (hL : 0 < L) (hLsq : ν * R ^ 2 = L ^ 2) {ρ : ℝ} (hρ : L ≤ ρ) :
    |deriv χ (ν * (R ^ 2 / ρ ^ 2)) * (-2 * ν * R ^ 2 / ρ ^ 3) / ρ| ≤ 2 * M1 * (L⁻¹) ^ 2 := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hL hρ
  have hpl : ρ⁻¹ ≤ L⁻¹ := inv_anti₀ hL hρ
  have hR2 : R ^ 2 = L ^ 2 / ν := eq_div_of_mul_eq hν.ne' (by rw [mul_comm]; exact hLsq)
  have hM1n : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hform : deriv χ (ν * (R ^ 2 / ρ ^ 2)) * (-2 * ν * R ^ 2 / ρ ^ 3) / ρ =
      (-2 * deriv χ (ν * (R ^ 2 / ρ ^ 2))) * (L ^ 2 * ρ⁻¹ ^ 4) := by
    rw [hR2]
    field_simp
  rw [hform, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ L ^ 2 * ρ⁻¹ ^ 4)]
  have h4 : L ^ 2 * ρ⁻¹ ^ 4 ≤ (L⁻¹) ^ 2 := by
    calc L ^ 2 * ρ⁻¹ ^ 4 ≤ L ^ 2 * (L⁻¹) ^ 4 := by gcongr
      _ = (L⁻¹) ^ 2 := by field_simp
  calc |(-2 : ℝ)| * |deriv χ (ν * (R ^ 2 / ρ ^ 2))| * (L ^ 2 * ρ⁻¹ ^ 4)
      ≤ 2 * M1 * (L⁻¹) ^ 2 := by
        rw [abs_neg, abs_two]
        gcongr
        exact hM1 _

end UnforcedLeray.Short.PartIIIb.Concrete

end
