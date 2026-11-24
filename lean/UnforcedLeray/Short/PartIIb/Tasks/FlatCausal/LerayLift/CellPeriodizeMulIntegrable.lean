import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/5/7`: cell integrability of an unfolded product

Source of record: `the November 2 reference manuscript` (SP 1901-1903, 1923-1926). Proves
the Prop `CellPeriodizeMulIntegrable` of `Sub/T12_2_5.lean`, the `[0,∞]` companion of
`Cyl.integral_cell_periodize_mul` (`Lib/CylinderB/Periodize.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem cellPeriodizeMulIntegrable_proof :
    UnforcedLeray.Short.IIb.LerayLiftSub.CellPeriodizeMulIntegrable := by
  intro c f g hc hf hg hPf hper hfg
  have hFm : Measurable (fun w : ℝ × ℝ => ‖f w * g w‖ₑ) :=
    ((hf.mul hg).measurable).enorm
  have hpt : ∀ z : ℝ × ℝ, ‖UnforcedLeray.Cyl.periodize c f z * g z‖ₑ ≤
      UnforcedLeray.Cyl.periodize c (fun w => ‖f w * g w‖ₑ) z := by
    intro z
    have hL : UnforcedLeray.Cyl.periodize c f z * g z = ∑' n : ℤ, f (z.1 - n * c, z.2) * g z := by
      rw [UnforcedLeray.Cyl.periodize, tsum_mul_right]
    rw [hL]
    refine (enorm_tsum_le_tsum_enorm).trans_eq ?_
    unfold UnforcedLeray.Cyl.periodize
    congr 1
    funext n
    have hgn : g (z.1 - n * c, z.2) = g z := by
      rw [← hper.add_int_mul (-n) z]
      congr 1
      exact Prod.ext (by push_cast; ring) rfl
    show ‖f (z.1 - n * c, z.2) * g z‖ₑ = ‖f (z.1 - n * c, z.2) * g (z.1 - n * c, z.2)‖ₑ
    rw [hgn]
  have hmeas : AEStronglyMeasurable (fun z => UnforcedLeray.Cyl.periodize c f z * g z)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    (hPf.mul hg).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  show ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖UnforcedLeray.Cyl.periodize c f z * g z‖ₑ < ⊤
  calc ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖UnforcedLeray.Cyl.periodize c f z * g z‖ₑ
      ≤ ∫⁻ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.periodize c (fun w => ‖f w * g w‖ₑ) z :=
        lintegral_mono (fun z => hpt z)
    _ = ∫⁻ z, ‖f z * g z‖ₑ := UnforcedLeray.Cyl.lintegral_cell_periodize hc hFm
    _ < ⊤ := hfg.2

end UnforcedLeray.Short.IIb.LerayLiftSub
