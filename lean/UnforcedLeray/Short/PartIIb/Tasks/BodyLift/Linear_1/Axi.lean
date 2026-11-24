import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1
import UnforcedLeray.Units.B0415
import UnforcedLeray.Short.PartIIb.Sub.R1_3
import UnforcedLeray.Cons.C03Background.Pieces

/-!
# `PartII-b:P1/1/1`, `BLRAxi`: the real slices of an `𝒪`-invariant `f` are axisymmetric without
swirl for a.e. phase.

Route: `f ∈ Osym` gives `f ∈ YO` (`act = actY`, `R1_3.act_eq_actY`), hence `f ∈ Yaxi`
(`Yaxi_eq_YO`), whose slices are `IsAxiNoSwirlC` for a.e. phase (`mem_Yaxi_iff_slices`, which uses
the countable generators: rational rotations and the reflection `reflY`, plus continuity of the
rotation orbit). The a.e. phase transfers to real phases (`PhaseTrace.ae_comp_mk`), and the real
part of the joint representative agrees a.e. with the slice (`rep_slice`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

theorem reP_eq_reV_pt (v : CVec3) : reP v = UnforcedLeray.RieszLp.reV v := by
  ext i
  simp [reP, UnforcedLeray.RieszLp.reV_apply]

theorem blrAxi_proof : BLRAxi := by
  intro p f
  have hmem : (f : Yq p.period q0E) ∈ forceSpace p.period := f.2
  have hosym : (f : Yq p.period q0E) ∈ Osym p.period q0E :=
    ((mem_forceSpace p.period).1 hmem).2.2
  have hYO : (f : Yq p.period q0E) ∈ UnforcedLeray.B0415.YO p.period q0E := by
    rw [UnforcedLeray.B0415.mem_YO]
    intro g hg
    rw [← act_eq_actY]
    exact (mem_Osym.1 hosym) g hg
  have hYaxi : (f : Yq p.period q0E) ∈ UnforcedLeray.B0415.Yaxi p.period q0E := by
    rw [UnforcedLeray.B0415.Yaxi_eq_YO]
    exact hYO
  have hsl := (UnforcedLeray.B0415.mem_Yaxi_iff_slices q0E_ne_top
    (f : Yq p.period q0E)).1 hYaxi
  have hline := UnforcedLeray.PhaseTrace.ae_comp_mk
    (p := fun x : AddCircle p.period =>
      UnforcedLeray.B0415.IsAxiNoSwirlC
        (((f : Yq p.period q0E) x : Lp CVec3 q0E (volume : Measure Space)) : Space → CVec3))
    hsl
  filter_upwards [hline] with τ hτ
  refine UnforcedLeray.Cons.C03.isAxisymmetricNoSwirl_congr_ae' hτ.1 ?_
  filter_upwards [rep_slice (f : Yq p.period q0E) τ] with y hy
  simp only [hy, reP_eq_reV_pt]

end UnforcedLeray.Short.IIb
