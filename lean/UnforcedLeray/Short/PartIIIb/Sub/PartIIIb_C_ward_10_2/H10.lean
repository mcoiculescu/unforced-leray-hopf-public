import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H9

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (10): the radial factor of the stream correction

Source of record: `the November 2 reference manuscript` (73 pages), 4180-4186:
`χ_y' = ∂_rχ_y = -2νR²r⁻³ χ̂_y'(νR²/r²)`; `χ̂_y' ≠ 0` only for `νR²/r² ∈ [4/5, 1]`, i.e.
`R√ν ≤ r ≤ R√(5ν/4)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The radial coefficient `(χ̂_y'(νR²/ρ²)·(-2νR²/ρ³))/ρ` of the stream correction. -/
def w2a (ν R : ℝ) (χy : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  deriv χy (ν * (R ^ 2 / ρ ^ 2)) * (-2 * ν * R ^ 2 / ρ ^ 3) / ρ

theorem wardStreamCorr_eq (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    wardStreamCorr ν R χy Z τ y = (w2a ν R χy (ϱ y) * outPrim Z τ (ϱ y) (y 2)) • coordinateVector 2 :=
  rfl

theorem w2_deriv_zero_of_lt {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) {t : ℝ} (ht : t < 4 / 5) :
    deriv χ t = 0 := by
  have : χ =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
    Filter.mem_of_superset (Iio_mem_nhds ht) fun s hs => hχ.one s (le_of_lt hs)
  rw [this.deriv_eq]; simp

theorem w2a_zero_of_le {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy) (hν : 0 < ν) (hR : 0 < R)
    {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ R * Real.sqrt ν) : w2a ν R χy ρ = 0 := by
  have hsq : ρ ^ 2 ≤ ν * R ^ 2 := by
    have := pow_le_pow_left₀ hρ.le h 2
    rw [mul_pow, Real.sq_sqrt hν.le] at this
    linarith
  have ht : 1 ≤ ν * (R ^ 2 / ρ ^ 2) := by
    rw [← mul_div_assoc, le_div_iff₀ (pow_pos hρ 2), one_mul]
    exact hsq
  unfold w2a
  rw [hχ.deriv_eq_zero ht]; simp

theorem w2a_zero_of_gt {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy) (hν : 0 < ν) (hR : 0 < R)
    {ρ : ℝ} (h : R * Real.sqrt (5 * ν / 4) < ρ) : w2a ν R χy ρ = 0 := by
  have hρ : 0 < ρ := lt_of_le_of_lt (by positivity) h
  have hsq : 5 * ν / 4 * R ^ 2 < ρ ^ 2 := by
    have := pow_lt_pow_left₀ h (by positivity) (two_ne_zero)
    rw [mul_pow, Real.sq_sqrt (by positivity)] at this
    linarith
  have ht : ν * (R ^ 2 / ρ ^ 2) < 4 / 5 := by
    rw [← mul_div_assoc, div_lt_iff₀ (pow_pos hρ 2)]
    nlinarith [mul_pos hν (pow_pos hR 2)]
  unfold w2a
  rw [w2_deriv_zero_of_lt hχ ht]; simp

theorem w2a_contDiffOn {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy) :
    ContDiffOn ℝ 1 (w2a ν R χy) (Ioi 0) := by
  have hdχ : ContDiff ℝ 1 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχ.smooth).deriv').of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hne : ∀ ρ ∈ Ioi (0 : ℝ), ρ ≠ 0 := fun ρ hρ => ne_of_gt hρ
  have h1 : ContDiffOn ℝ 1 (fun ρ : ℝ => ν * (R ^ 2 / ρ ^ 2)) (Ioi 0) :=
    contDiffOn_const.mul (contDiffOn_const.div (contDiffOn_id.pow 2) fun ρ hρ => pow_ne_zero 2 (hne ρ hρ))
  have h2 : ContDiffOn ℝ 1 (fun ρ : ℝ => -2 * ν * R ^ 2 / ρ ^ 3) (Ioi 0) :=
    contDiffOn_const.div (contDiffOn_id.pow 3) fun ρ hρ => pow_ne_zero 3 (hne ρ hρ)
  unfold w2a
  exact ((hdχ.comp_contDiffOn h1).mul h2).div contDiffOn_id hne

theorem w2a_deriv_zero_of_gt {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) {ρ : ℝ} (h : R * Real.sqrt (5 * ν / 4) < ρ) : deriv (w2a ν R χy) ρ = 0 := by
  have : w2a ν R χy =ᶠ[𝓝 ρ] fun _ => (0 : ℝ) :=
    Filter.mem_of_superset (Ioi_mem_nhds h) fun s hs => w2a_zero_of_gt hχ hν hR hs
  rw [this.deriv_eq]; simp

/-- Bounds of the radial factor and its derivative on the annulus. -/
theorem w2a_bound {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy) (hν : 0 < ν) (hR : 0 < R) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧ ∀ ρ : ℝ, R * Real.sqrt ν ≤ ρ → ρ ≤ R * Real.sqrt (5 * ν / 4) →
      |w2a ν R χy ρ| ≤ Ca ∧ |deriv (w2a ν R χy) ρ| ≤ Cb := by
  set r1 := R * Real.sqrt ν with hr1
  set r2 := R * Real.sqrt (5 * ν / 4) with hr2
  have hr1pos : 0 < r1 := by positivity
  have hcd := w2a_contDiffOn (ν := ν) (R := R) hχ
  have hcA : ContinuousOn (w2a ν R χy) (Icc r1 r2) :=
    hcd.continuousOn.mono fun ρ hρ => lt_of_lt_of_le hr1pos hρ.1
  have hcB : ContinuousOn (deriv (w2a ν R χy)) (Icc r1 r2) :=
    (hcd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono fun ρ hρ => lt_of_lt_of_le hr1pos hρ.1
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn hcA
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcB
  refine ⟨max Ca 0, max Cb 0, le_max_right _ _, le_max_right _ _, fun ρ h1 h2 => ?_⟩
  refine ⟨?_, ?_⟩
  · have := (hCa ρ ⟨h1, h2⟩).trans (le_max_left Ca 0)
    rwa [Real.norm_eq_abs] at this
  · have := (hCb ρ ⟨h1, h2⟩).trans (le_max_left Cb 0)
    rwa [Real.norm_eq_abs] at this

end UnforcedLeray.Short.PartIIIb.Concrete
end
