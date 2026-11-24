import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# `PartII-b:T10/6/1/2`: `GActPhaseTest` (`g·` preserves phase tests, SP 1912-1915)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GActLeaf2

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

end UnforcedLeray.Short.IIb.GActLeaf2

theorem gActPhaseTest : UnforcedLeray.Short.IIb.GActPhaseTest := by
  unfold UnforcedLeray.Short.IIb.GActPhaseTest
  intro P g Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · unfold UnforcedLeray.Short.IIb.gAct
    have hG : ContDiff ℝ ∞ (UnforcedLeray.B0412.gC g) :=
      ContinuousLinearMap.contDiff ((UnforcedLeray.B0412.gC g).restrictScalars ℝ)
    have hL : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
        (x.1, g.symm x.2)) :=
      contDiff_fst.prodMk ((g.symm.toContinuousLinearEquiv.contDiff).comp contDiff_snd)
    exact hG.comp (hΦ.smooth.comp hL)
  · intro τ y
    unfold UnforcedLeray.Short.IIb.gAct
    simp only [hΦ.periodic]
  · obtain ⟨R, hR⟩ := hΦ.bounded_support
    refine ⟨R, ?_⟩
    intro τ y hy
    unfold UnforcedLeray.Short.IIb.gAct
    rw [hR τ (g.symm y) (by rw [LinearIsometryEquiv.norm_map]; exact hy), map_zero]
