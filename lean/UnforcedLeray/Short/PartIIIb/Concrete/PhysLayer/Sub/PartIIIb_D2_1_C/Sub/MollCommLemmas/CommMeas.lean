import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.MollIntegralSplit

/-!
# `CommMeas`: measurability of the commutator

Source `the November 2 reference manuscript` (adjoint graph at `r = 2` and the
mollified commutator; the cited line numbers of the task spec do not match the current file, the
mathematics is that of the docstrings in `MollCommDefs`). `commK ρ F x = ∫ ½ kap ρ z • F(x - z) dz`
is the integral over the second variable of the jointly measurable function
`(x, z) ↦ ½ kap ρ z • F(x - z)`: the kernel is continuous, `F` is a.e. strongly measurable, and
`(x, z) ↦ x - z` is quasi measure preserving for the product of Lebesgue measures. Then
`AEStronglyMeasurable.integral_prod_right'` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- `x ↦ ∫ ½ kap ρ z • F(x - z) dz` is a.e. strongly measurable for an a.e. strongly measurable
`F`. -/
theorem cm_commK_aesm (ρ : ContDiffBump (0 : ℝ × Space)) {F : ℝ × Space → CVec3}
    (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (commK ρ F) volume := by
  have hc : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) * kap ρ z) := (mis_halfKap_props ρ).1
  have hH : AEStronglyMeasurable
      (fun p : (ℝ × Space) × (ℝ × Space) => ((1 / 2 : ℝ) * kap ρ p.2) • F (p.1 - p.2))
      (volume.prod volume) :=
    ((hc.comp continuous_snd).aestronglyMeasurable).smul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  exact hH.integral_prod_right'

theorem commMeas : CommMeas := by
  intro P hP ρ F hF
  rcases hF with hY | hΨ
  · exact cm_commK_aesm ρ hY.meas
  · exact cm_commK_aesm ρ hΨ.smooth.continuous.aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
