import UnforcedLeray.Units.B0226.AxisCutoff

/-!
# A two-sided cutoff in the `η` variable (helper for `LerayGradPerp`)

`chi t = 1 - κ(t² - 1)` with the profile cutoff `κ = B0226.kappa`: `chi = 1` for `t² ≤ 2`,
`chi = 0` for `t² ≥ 3`, and `chi` is locally constant off `[√2, √3]` (so `deriv chi` vanishes
outside `2 ≤ t² ≤ 3`), with `deriv chi` bounded (continuous with compact support).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut

/-- The cutoff `chi(t) = 1 - κ(t² - 1)`. -/
def chi (t : ℝ) : ℝ := 1 - UnforcedLeray.B0226.kappa (t ^ 2 - 1)

theorem contDiff_chi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi :=
  contDiff_const.sub ((UnforcedLeray.B0226.contDiff_kappa).comp
    ((contDiff_id.pow 2).sub contDiff_const))

theorem chi_one {t : ℝ} (h : t ^ 2 ≤ 2) : chi t = 1 := by
  unfold chi
  rw [UnforcedLeray.B0226.kappa_eq_zero (by linarith)]
  ring

theorem chi_zero {t : ℝ} (h : 3 ≤ t ^ 2) : chi t = 0 := by
  unfold chi
  rw [UnforcedLeray.B0226.kappa_eq_one (by linarith)]
  ring

theorem chi_nonneg (t : ℝ) : 0 ≤ chi t := by
  unfold chi
  linarith [UnforcedLeray.B0226.kappa_le_one (t ^ 2 - 1)]

theorem chi_le_one (t : ℝ) : chi t ≤ 1 := by
  unfold chi
  linarith [UnforcedLeray.B0226.kappa_nonneg (t ^ 2 - 1)]

theorem deriv_chi_of_lt {t : ℝ} (h : t ^ 2 < 2) : deriv chi t = 0 := by
  have hev : chi =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds h] with x hx
    exact chi_one (le_of_lt (show x ^ 2 < 2 from hx))
  rw [hev.deriv_eq, deriv_const]

theorem deriv_chi_of_gt {t : ℝ} (h : 3 < t ^ 2) : deriv chi t = 0 := by
  have hev : chi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.pow 2)).mem_nhds h] with x hx
    exact chi_zero (le_of_lt (show 3 < x ^ 2 from hx))
  rw [hev.deriv_eq, deriv_const]

theorem sq_bounds_of_deriv_ne {t : ℝ} (h : deriv chi t ≠ 0) : 2 ≤ t ^ 2 ∧ t ^ 2 ≤ 3 := by
  constructor
  · by_contra h'
    exact h (deriv_chi_of_lt (not_le.mp h'))
  · by_contra h'
    exact h (deriv_chi_of_gt (not_le.mp h'))

theorem chi_hasCompactSupport : HasCompactSupport chi := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) (fun x hx => ?_)
  apply chi_zero
  rcases not_and_or.mp (show ¬ (-2 ≤ x ∧ x ≤ 2) from fun h => hx ⟨h.1, h.2⟩) with h | h
  · nlinarith [not_le.mp h]
  · nlinarith [not_le.mp h]

theorem exists_bound_deriv_chi : ∃ B : ℝ, ∀ t : ℝ, |deriv chi t| ≤ B := by
  have hc : Continuous (deriv chi) := contDiff_chi.continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv chi) := chi_hasCompactSupport.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC t⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut
