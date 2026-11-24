import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# The Floquet window stays above `-1/4`

Source `the November 2 reference manuscript` 5946 (window `μ_n(z) = σ₀ + z/(2|log ν_n|)`),
used for the window bound `μ > -1/4` of 3631-3646 and 5946.

Under the standing hypotheses `σ₀ > 0` and `ν_n → 0` (`retNu_tendsto`), `|log ν_n| → ∞`; for large `n`
`|log ν_n| ≥ 2`, so for `|z| ≤ 1` the correction `z/(2|log ν_n|)` is at least `-1/4`, and
`μ_n(z) ≥ σ₀ - 1/4 > -1/4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem muWin_gt_quarter (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, -(1 / 4) < D.mu n z := by
  have hσ : 0 < D.σ₀ := hst.sigma_pos
  have hν : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨retNu_tendsto (Pl := D.Pl) D.σ₀ hst.omega_ne,
      Eventually.of_forall (fun n => retNu_pos D.Pl D.σ₀ n)⟩
  have hlog : Tendsto (fun n => Real.log (retNu D.Pl D.σ₀ n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hν
  have hev : ∀ᶠ n : ℕ in atTop, Real.log (retNu D.Pl D.σ₀ n) < -2 :=
    hlog.eventually_lt_atBot (-2)
  filter_upwards [hev] with n hn
  intro z hz
  obtain ⟨hz1, _hz2⟩ := hz
  have hL : |Real.log (retNu D.Pl D.σ₀ n)| = -Real.log (retNu D.Pl D.σ₀ n) :=
    abs_of_neg (by linarith)
  have hLge : 2 ≤ |Real.log (retNu D.Pl D.σ₀ n)| := by
    rw [hL]; linarith
  show -(1 / 4) < muWin D.σ₀ (retNu D.Pl D.σ₀ n) z
  unfold muWin
  have hpos : 0 < 2 * |Real.log (retNu D.Pl D.σ₀ n)| := by linarith
  have key : -(1 / 4 : ℝ) ≤ z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
