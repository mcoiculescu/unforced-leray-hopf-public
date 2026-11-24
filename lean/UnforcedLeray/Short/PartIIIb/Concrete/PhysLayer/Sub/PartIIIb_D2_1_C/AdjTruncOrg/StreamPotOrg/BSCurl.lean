import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCurlSlice
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceCurl
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceSol
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsPhaseSliceTest

/-!
# `curl (bsPot Φ) = Φ` (BSCurl)

Source `the November 2 reference manuscript` lines 1351-1362. For a weakly
solenoidal `Φ ∈ Y_2`, the stream potential `ψ = bsPot Φ` satisfies `curl ψ = Φ` weakly.

Proof: for a phase test `Θ`, both sides of `pairF P (curlT Θ) (bsPot Φ) = pairF P Θ Φ` are
phase integrals. For a.e. phase `t` the slice `Φ(t, ·)` is in `L²` and solenoidal, `Θ(t, ·)` is
smooth and compactly supported, `curlT Θ (t, ·) = bsCurlS Θ(t, ·)`, and `bsPot Φ (t, ·)` is the
slice Biot-Savart potential; the slice identity `bsSliceCurl` then gives equality of the `y`
integrals for a.e. `t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem bsCurl : BSCurl := by
  intro P hP Φ hΦ hsol Θ hΘ
  unfold UnforcedLeray.Cons.C03.Concrete.pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [bsSliceL2 P hP Φ hΦ, bsSliceSol P hP Φ hΦ hsol] with t h2 h3 _
  have hcurl : ∀ y : Space, curlT Θ (t, y) = bsCurlS (fun y' : Space => Θ (t, y')) y :=
    fun y => bsCurlSlice P Θ hΘ t y
  have hb : ∀ y : Space, bsPot Φ (t, y) = bsSlice (fun z : Space => Φ (t, z)) y :=
    fun y => rfl
  have hs := bsPhaseSliceTest P Θ hΘ t
  simp only [hcurl, hb]
  exact bsSliceCurl (fun z : Space => Φ (t, z)) h2 h3 (fun y : Space => Θ (t, y)) hs.1 hs.2

end UnforcedLeray.Short.PartIIIb.Concrete
