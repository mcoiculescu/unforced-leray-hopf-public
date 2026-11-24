import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Lib.CylinderB.Periodize

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem cell_eq_cyl_kv (d : ℝ) : UnforcedLeray.B0579.cell d = UnforcedLeray.Cyl.cell d := by
  unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem kerVelConv : KerVelConv := by
  intro d hd ψ hψ x l
  obtain ⟨C, _, hC⟩ := kerNearFar
  have hd0 : 0 < d := by linarith
  have hk : UnforcedLeray.Cyl.IsPeriodic d (fun z => kerD d z l) := fun z => (hC d hd).2.1 z l
  have hf : UnforcedLeray.Cyl.IsPeriodic d ψ := fun z => hψ.periodic z
  unfold kerVel
  have h1 : ∫ y in UnforcedLeray.B0579.cell d, ψ y * kerD d (x - y) l
      = ∫ y in UnforcedLeray.Cyl.cell d, (fun z => kerD d z l) (x - y) • ψ y := by
    rw [cell_eq_cyl_kv d]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    ring
  rw [h1, UnforcedLeray.Cyl.integral_cell_mul_comp_sub hd0 hk hf x, ← cell_eq_cyl_kv d]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]

end UnforcedLeray.Short.IIIa
