import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window

/-!
# `muWinLeOne`: the Floquet window stays below `1`

Source `the November 2 reference manuscript` 5946 (window `μ_n(z) = σ₀ + z/(2|log ν_n|)`,
`σ₀ < 1/4`). Same structure as `muWin_gt_quarter` (`../Window.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem muWinLeOne : MuWinLeOne := by
  intro D dm dp hst
  have hν : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨retNu_tendsto (Pl := D.Pl) D.σ₀ hst.omega_ne,
      Eventually.of_forall (fun n => retNu_pos D.Pl D.σ₀ n)⟩
  have hlog : Tendsto (fun n => Real.log (retNu D.Pl D.σ₀ n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hν
  have hev : ∀ᶠ n : ℕ in atTop, Real.log (retNu D.Pl D.σ₀ n) < -2 :=
    hlog.eventually_lt_atBot (-2)
  have hσ1 : D.σ₀ < 1 / 4 := hst.sigma_lt
  filter_upwards [hev] with n hn
  intro z hz
  obtain ⟨_hz1, hz2⟩ := hz
  have hL : |Real.log (retNu D.Pl D.σ₀ n)| = -Real.log (retNu D.Pl D.σ₀ n) :=
    abs_of_neg (by linarith)
  have hLge : 2 ≤ |Real.log (retNu D.Pl D.σ₀ n)| := by
    rw [hL]; linarith
  show D.σ₀ + z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|) ≤ 1
  have hpos : 0 < 2 * |Real.log (retNu D.Pl D.σ₀ n)| := by linarith
  have key : z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|) ≤ 1 / 4 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
