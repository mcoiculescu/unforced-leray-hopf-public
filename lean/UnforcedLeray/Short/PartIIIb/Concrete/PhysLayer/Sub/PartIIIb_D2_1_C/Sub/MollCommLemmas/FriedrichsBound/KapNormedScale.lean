import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_9

/-!
# `kapNormedScale`: dilation covariance of the normalised Friedrichs bump

Source `the November 2 reference manuscript` lines 1556-1583 (the Friedrichs
commutator needs only an absolute constant).  For a `ContDiffBump` `ρ` with `rOut = 2 rIn`, the
normalised bump is the dilate of the normalised unit bump `kapUnit`:
`ρ.normed z = rIn⁻⁴ · kapUnit.normed (rIn⁻¹ z)`.

Proof: `ContDiffBump.apply` gives `ρ w = β 2 (rIn⁻¹ w)` and `kapUnit w = β 2 w`, so `ρ w = kapUnit (rIn⁻¹ w)`;
then `∫ ρ = rIn⁴ ∫ kapUnit` by `Measure.integral_comp_inv_smul` with `finrank (ℝ × Space) = 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem kapNormedScale (ρ : ContDiffBump (0 : ℝ × Space)) (hρ : ρ.rOut = 2 * ρ.rIn) (z : ℝ × Space) : ρ.normed volume z = (ρ.rIn ^ 4)⁻¹ * kapUnit.normed volume (ρ.rIn⁻¹ • z) := by
  have hr : 0 < ρ.rIn := ρ.rIn_pos
  have hfr : Module.finrank ℝ (ℝ × Space) = 4 := by
    rw [Module.finrank_prod, UnforcedLeray.Conv.finrank_space]
    simp
  have hq : ρ.rOut / ρ.rIn = 2 := by
    rw [hρ, mul_div_assoc, div_self hr.ne', mul_one]
  have hq' : kapUnit.rOut / kapUnit.rIn = 2 := by
    norm_num [kapUnit]
  have hpt : ∀ w : ℝ × Space, ρ w = kapUnit (ρ.rIn⁻¹ • w) := by
    intro w
    have h1 : ρ w = (someContDiffBumpBase (ℝ × Space)).toFun (ρ.rOut / ρ.rIn) (ρ.rIn⁻¹ • (w - 0)) :=
      ρ.apply w
    have h2 : kapUnit (ρ.rIn⁻¹ • w) = (someContDiffBumpBase (ℝ × Space)).toFun
        (kapUnit.rOut / kapUnit.rIn) (kapUnit.rIn⁻¹ • (ρ.rIn⁻¹ • w - 0)) :=
      kapUnit.apply _
    have hk : kapUnit.rIn = 1 := rfl
    rw [h1, h2, hq, hq']
    simp [hk]
  have hint : (∫ x, ρ x ∂(volume : Measure (ℝ × Space))) =
      ρ.rIn ^ 4 * ∫ x, kapUnit x ∂(volume : Measure (ℝ × Space)) := by
    have hf : (fun x => ρ x) = fun x => kapUnit (ρ.rIn⁻¹ • x) := funext hpt
    rw [hf, Measure.integral_comp_inv_smul (μ := (volume : Measure (ℝ × Space)))
      (fun x => kapUnit x) ρ.rIn, hfr, smul_eq_mul, abs_of_nonneg (by positivity)]
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, hint, hpt z]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
