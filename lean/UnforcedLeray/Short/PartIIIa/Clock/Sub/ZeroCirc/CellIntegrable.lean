import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves
import UnforcedLeray.Units.B0273.Mean

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem zcCellIntegrable : ZCCellIntegrable := by
  intro c m hm g hg
  have hn : MemLp (fun x => ‖g x‖) 2 (B0579.cellMeasure c m) := hg.norm
  have hI : IntegrableOn ((hn.toLp _ : B0579.X c m) : B0579.Plane → ℝ) (B0579.cell c) :=
    B0273.integrableOn_cell_X hm (hn.toLp _)
  have hae : ((hn.toLp _ : B0579.X c m) : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => ‖g x‖ :=
    (B0579.ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hn)
  have hnI : IntegrableOn (fun x => ‖g x‖) (B0579.cell c) := hI.congr hae
  exact Integrable.mono' hnI (hg.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m))
    (Eventually.of_forall fun x => by simp)

end UnforcedLeray.Short.IIIa
