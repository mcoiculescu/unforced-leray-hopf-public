import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotDecay.Helpers

/-!
# Decay of `∇u` in `η` (`LerayPotDecay`)

Source `the November 2 reference manuscript` 1676.  The derivatives of the potential are
`∂_j u = lerayPot c (∂_j F)` (`LerayPotSmooth`), and each such potential decays like `e^{-a|η|}`
(`dd_decay_gen` in `LerayPotDecay/Helpers.lean`), using `∫_cell ∂_j F₁ = 0` (`dd_int_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Decay of `∇u`**: `|∂_q u| + |∂_η u| ≤ C e^{-κ|η|}` with `κ = a = cylFreq c`. -/
theorem lerayPotDecay : LerayPotDecay := by
  intro c hc F hF
  obtain ⟨C1, hC1⟩ := dd_decay_gen c hc (dfDv F ((0 : ℝ), dir2 0))
    (forceFieldDeriv c F hF _) (fun p => dd_int_zero c hc F hF p 0)
  obtain ⟨C2, hC2⟩ := dd_decay_gen c hc (dfDv F ((0 : ℝ), dir2 1))
    (forceFieldDeriv c F hF _) (fun p => dd_int_zero c hc F hF p 1)
  refine ⟨C1 + C2, cylFreq c, dd_freq_pos c hc, fun p => ?_⟩
  have e1 : UnforcedLeray.Axi.dQ (lerayPot c F) p = lerayPot c (dfDv F ((0 : ℝ), dir2 0)) p :=
    (lerayPotSmooth c hc F hF).2.2 p ((0 : ℝ), dir2 0)
  have e2 : UnforcedLeray.Axi.dEta (lerayPot c F) p = lerayPot c (dfDv F ((0 : ℝ), dir2 1)) p :=
    (lerayPotSmooth c hc F hF).2.2 p ((0 : ℝ), dir2 1)
  rw [e1, e2]
  have h1 := hC1 p
  have h2 := hC2 p
  calc |lerayPot c (dfDv F ((0 : ℝ), dir2 0)) p| + |lerayPot c (dfDv F ((0 : ℝ), dir2 1)) p|
      ≤ C1 * Real.exp (-(cylFreq c * |p.2.2|)) + C2 * Real.exp (-(cylFreq c * |p.2.2|)) :=
        add_le_add h1 h2
    _ = (C1 + C2) * Real.exp (-(cylFreq c * |p.2.2|)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
