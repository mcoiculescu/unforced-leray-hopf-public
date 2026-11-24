import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv.AdvT
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv.Diff
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv.Lift

/-!
# Part II-b, task `PartII-b:G4/3/4/1` (`chartAdvPtw`)

Source of record: `the November 2 reference manuscript`, SP 1919-1921, 2007-2012.
The polarized advection identity `ChartAdvPtw` (stated with `0 < R`) follows from the four
lemmas of the organization:

* `chartAdv_advT` (A): each `advT` of the ring lifts is the lift of the advection;
* `chartAdv_diffAt` (B): joint differentiability of the ring lift off the axis;
* `chartAdv_dRho_dz` (C), used inside `chartAdv_lift` (D): the chain rule through `Q_ε`, `∂_η`;
  the final identity is `chartAdv_lift` (D) read through `realC`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **`PartII-b:G4/3/4/1`**: the polarized advection identity for two no-swirl ring lifts in the
chart, for `R > 0`. -/
theorem chartAdvPtw : UnforcedLeray.Short.IIb.ChartAdvPtw := by
  unfold UnforcedLeray.Short.IIb.ChartAdvPtw
  intro R hR b d τ y hy hb hd
  have hR0 : R ≠ 0 := hR.ne'
  have hdd : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) (τ, y) :=
    (chartAdv_diffAt R hR d τ y hy hd).1
  have hdb : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.Nv R b x.1 x.2) (τ, y) :=
    (chartAdv_diffAt R hR b τ y hy hb).1
  rw [chartAdv_advT R b d τ y hdd, chartAdv_advT R d b τ y hdb]
  rw [← chartAdv_lift R hR b d τ y hy hb hd]
  ext i
  simp [UnforcedLeray.B0412.realC_apply]

end UnforcedLeray.Short.IIb
