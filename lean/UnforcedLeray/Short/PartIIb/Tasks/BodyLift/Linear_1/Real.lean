import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedFieldRepMinimalAE
import UnforcedLeray.Lib.LerayC.Complex

/-!
# `PartII-b:P1/1/1`, `BLRReal`: real elements of `Y_{q₀}` have real joint representatives a.e.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

theorem ofReV_reV_eq_realC_reP (v : CVec3) :
    UnforcedLeray.RieszLp.ofReV (UnforcedLeray.RieszLp.reV v) = realC (reP v) := by
  ext i
  simp [UnforcedLeray.RieszLp.ofReV_apply, realC_apply, reP, UnforcedLeray.RieszLp.reV_apply]

theorem blrReal_proof : BLRReal := by
  intro p f
  have hmem : (f : Yq p.period q0E) ∈ forceSpace p.period := f.2
  have hreal : (f : Yq p.period q0E) ∈ realSub p.period q0E := ((mem_forceSpace p.period).1 hmem).1
  have hae := rep_real_ae_of_realSub (f : Yq p.period q0E) hreal
  rw [Measure.volume_eq_prod]
  filter_upwards [hae] with x hx
  exact hx.trans (ofReV_reV_eq_realC_reP _)

end UnforcedLeray.Short.IIb
