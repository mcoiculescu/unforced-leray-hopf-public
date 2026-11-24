import UnforcedLeray.Short.PartI.Sub.C09
import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction.Radial
import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction.Polar2D

/-!


`polarReduction : PolarReduction` (source lines 1139-1140 of
`the November 2 reference manuscript`; the Lean definition is in `C09.lean`).

Proof outline.  For a test function `φ` supported away from `0`, the angular mode
`Φ(r) = ∫_{-π}^{π} e^{2iθ} φ(r cos θ, r sin θ) dθ` is smooth, vanishes for `r` outside a compact
subinterval of `(0, ∞)`, and satisfies `Φ'' + Φ'/r - 4Φ/r² = ∫ e^{2iθ} Δφ` (`angular_identity`).
The polar formula (`polar_pairing`) turns both planar pairings into radial integrals, and the
radial weak equation `RadialWeakEq ψ f` applied to `Φ` closes the argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff
open UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob
open UnforcedLeray.Short.PartI.PolarRed

namespace UnforcedLeray.Short.PartI

theorem polarReduction : PolarReduction := by
  unfold PolarReduction
  intro ψ f hψ hf hrad
  unfold WeakLapOn
  intro φ hφt
  have hφs : ContDiff ℝ ∞ φ := hφt.smooth
  have hφc : Continuous φ := hφs.continuous
  -- the support of `φ` and of its Laplacian away from `0`
  set K := tsupport φ with hK_def
  have hKc : IsCompact K := hφt.compact.isCompact
  have h0 : (0 : ℝ × ℝ) ∉ K := fun h => hφt.subset h rfl
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport φ).isOpen_compl 0 h0
  obtain ⟨R0, hR0⟩ := hKc.isBounded.subset_closedBall 0
  set R := max R0 0 with hR_def
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  -- membership bounds for `pol`
  have norm_pol_le : ∀ r θ : ℝ, 0 ≤ r → ‖pol r θ‖ ≤ r := by
    intro r θ hr
    have h1 : ‖(pol r θ).1‖ ≤ r := by
      show ‖r * Real.cos θ‖ ≤ r
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
      nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ)]
    have h2 : ‖(pol r θ).2‖ ≤ r := by
      show ‖r * Real.sin θ‖ ≤ r
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
      nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
    rw [Prod.norm_def]
    exact max_le h1 h2
  -- inner support: `pol r θ ∉ K` for `0 < r < ε`
  have hin : ∀ r θ : ℝ, 0 < r → r < ε → pol r θ ∉ K := by
    intro r θ hr hrε hmem
    have hn : ‖pol r θ‖ < ε := lt_of_le_of_lt (norm_pol_le r θ hr.le) hrε
    exact (hball (mem_ball_zero_iff.2 hn)) hmem
  -- outer support: `pol r θ ∉ K` for `2R < r`
  have hout : ∀ r θ : ℝ, 2 * R < r → pol r θ ∉ K := by
    intro r θ hr hmem
    have hn : ‖pol r θ‖ ≤ R0 := by
      have := hR0 hmem
      simpa using this
    have hnR : ‖pol r θ‖ ≤ R := le_trans hn (le_max_left _ _)
    have h1 : |r * Real.cos θ| ≤ R := by
      have := norm_fst_le (pol r θ)
      have e : ‖(pol r θ).1‖ = |r * Real.cos θ| := Real.norm_eq_abs _
      rw [← e]
      exact le_trans this hnR
    have h2 : |r * Real.sin θ| ≤ R := by
      have := norm_snd_le (pol r θ)
      have e : ‖(pol r θ).2‖ = |r * Real.sin θ| := Real.norm_eq_abs _
      rw [← e]
      exact le_trans this hnR
    have hsq : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
    have h1' : (r * Real.cos θ) ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h2' : (r * Real.sin θ) ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith [mul_pos (sub_pos.2 hr) (by linarith : (0 : ℝ) < r + 2 * R)]
  -- radii
  set b := max (2 * R) ε with hb_def
  have hab : ε ≤ b := le_max_right _ _
  have hnot : ∀ r θ : ℝ, 0 < r → (r < ε ∨ b < r) → pol r θ ∉ K := by
    intro r θ hr hcase
    rcases hcase with h | h
    · exact hin r θ hr h
    · exact hout r θ (lt_of_le_of_lt (le_max_left _ _) h)
  -- the planar functions vanish off `K`
  have zero_off : ∀ z : ℝ × ℝ, z ∉ K → φ z = 0 ∧
      iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z = 0 := by
    intro z hz
    refine ⟨image_eq_zero_of_notMem_tsupport hz, ?_⟩
    have h1 : z ∉ tsupport (fderiv ℝ φ) := fun h => hz (tsupport_fderiv_subset ℝ h)
    have h2 : z ∉ tsupport (fderiv ℝ (fderiv ℝ φ)) :=
      fun h => h1 (tsupport_fderiv_subset ℝ h)
    have hD2 : fderiv ℝ (fderiv ℝ φ) z = 0 := image_eq_zero_of_notMem_tsupport h2
    have e0 : iterDirDeriv [ev 0, ev 0] φ z = fderiv ℝ (fderiv ℝ φ) z (ev 0) (ev 0) :=
      fderiv_apply_const hφs z (ev 0) (ev 0)
    have e1 : iterDirDeriv [ev 1, ev 1] φ z = fderiv ℝ (fderiv ℝ φ) z (ev 1) (ev 1) :=
      fderiv_apply_const hφs z (ev 1) (ev 1)
    rw [e0, e1, hD2]
    simp
  -- continuity of the Laplacian
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (ContDiff.fderiv_right (m := ∞) (ContDiff.fderiv_right (m := ∞) hφs (by simp))
      (by simp)).continuous
  have hMc : Continuous (fun z : ℝ × ℝ =>
      iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z) := by
    have e : (fun z : ℝ × ℝ => iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z) =
        fun z => fderiv ℝ (fderiv ℝ φ) z (ev 0) (ev 0) + fderiv ℝ (fderiv ℝ φ) z (ev 1) (ev 1) := by
      funext z
      have e0 : iterDirDeriv [ev 0, ev 0] φ z = fderiv ℝ (fderiv ℝ φ) z (ev 0) (ev 0) :=
        fderiv_apply_const hφs z (ev 0) (ev 0)
      have e1 : iterDirDeriv [ev 1, ev 1] φ z = fderiv ℝ (fderiv ℝ φ) z (ev 1) (ev 1) :=
        fderiv_apply_const hφs z (ev 1) (ev 1)
      rw [e0, e1]
    rw [e]
    exact ((hD2c.clm_apply continuous_const).clm_apply continuous_const).add
      ((hD2c.clm_apply continuous_const).clm_apply continuous_const)
  -- the polar pairings
  have hsuppM : ∀ r θ : ℝ, 0 < r → (r < ε ∨ b < r) →
      (iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ)) = 0 :=
    fun r θ hr hcase => (zero_off _ (hnot r θ hr hcase)).2
  have hsuppφ : ∀ r θ : ℝ, 0 < r → (r < ε ∨ b < r) → φ (pol r θ) = 0 :=
    fun r θ hr hcase => (zero_off _ (hnot r θ hr hcase)).1
  have hP1 : ∫ z, UnforcedLeray.B0010.angularTwoField ψ z *
      (iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z) =
      ∫ r in Ioi (0 : ℝ), r * ψ r * ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        (iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ)) :=
    polar_pairing ψ hψ _ hMc hε0 hab hsuppM
  have hP2 : ∫ z, UnforcedLeray.B0010.angularTwoField f z * φ z =
      ∫ r in Ioi (0 : ℝ), r * f r * ∫ θ in (-π)..π,
        Complex.exp (2 * Complex.I * (θ : ℂ)) * φ (pol r θ) :=
    polar_pairing f hf φ hφc hε0 hab hsuppφ
  -- the radial weak equation for the angular mode `Φ`
  have hΦs : ContDiffOn ℝ ∞ (fun r : ℝ => ∫ θ in (-π)..π, angF φ (r, θ)) (Ioi 0) :=
    (contDiff_param_infty (contDiff_angF hφs)).contDiffOn
  have hΦsupp : ∃ a c : ℝ, 0 < a ∧ ∀ r : ℝ, 0 < r → (r < a ∨ c < r) →
      (∫ θ in (-π)..π, angF φ (r, θ)) = 0 := by
    refine ⟨ε, b, hε0, fun r hr hcase => ?_⟩
    have hz : (fun θ : ℝ => angF φ (r, θ)) = fun _ => 0 := by
      funext θ
      simp only [angF]
      rw [hsuppφ r θ hr hcase]
      simp
    rw [hz]
    simp
  have hRW : ∫ r in Ioi (0 : ℝ), ψ r * (deriv (deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ))) r +
        deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ)) r / (r : ℂ) -
          4 * (∫ θ in (-π)..π, angF φ (r, θ)) / (r : ℂ) ^ 2) * (r : ℂ) =
      ∫ r in Ioi (0 : ℝ), f r * (∫ θ in (-π)..π, angF φ (r, θ)) * (r : ℂ) :=
    hrad (fun r : ℝ => ∫ θ in (-π)..π, angF φ (r, θ)) hΦs hΦsupp
  have eL : ∫ r in Ioi (0 : ℝ), r * ψ r * ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        (iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ)) =
      ∫ r in Ioi (0 : ℝ), ψ r * (deriv (deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ))) r +
        deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ)) r / (r : ℂ) -
          4 * (∫ θ in (-π)..π, angF φ (r, θ)) / (r : ℂ) ^ 2) * (r : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hid := angular_identity hφs hr0
    try dsimp only
    rw [← hid]
    ring
  have eR : ∫ r in Ioi (0 : ℝ), r * f r * ∫ θ in (-π)..π,
        Complex.exp (2 * Complex.I * (θ : ℂ)) * φ (pol r θ) =
      ∫ r in Ioi (0 : ℝ), f r * (∫ θ in (-π)..π, angF φ (r, θ)) * (r : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    simp only [angF]
    ring
  rw [hP1, hP2, eL, eR]
  exact hRW

end UnforcedLeray.Short.PartI
