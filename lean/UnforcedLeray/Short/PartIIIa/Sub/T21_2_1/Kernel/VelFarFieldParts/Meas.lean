import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_7

/-!
# Part III-a, `KerVelMeas`: measurability of the kernel velocity (SP 3052-3057)

`x ↦ ∫_{C_d} ψ(y) K_d(x - y) j dy` is a parametric integral of a jointly measurable integrand,
hence strongly measurable on the cell (no integrability is needed for measurability).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerVelMeas : UnforcedLeray.Short.IIIa.KerVelMeas := by
  intro d hd ψ hψ j
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hkm : Measurable fun z : ℝ × ℝ => kerD d z j :=
    ((PiLp.continuous_apply 2 _ j).measurable).comp (UnforcedLeray.Cyl.measurable_bsKernel d)
  have hF : StronglyMeasurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => ψ p.2 * kerD d (p.1 - p.2) j := by
    refine Measurable.stronglyMeasurable ?_
    exact (hψm.comp measurable_snd).mul (hkm.comp (measurable_fst.sub measurable_snd))
  exact (hF.integral_prod_right' (ν := volume.restrict (UnforcedLeray.B0579.cell d))).aestronglyMeasurable

end UnforcedLeray.Short.IIIa
