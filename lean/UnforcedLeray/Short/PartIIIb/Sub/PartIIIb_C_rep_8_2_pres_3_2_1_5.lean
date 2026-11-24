import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_1
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt

/-!
# `liftPExt` (`PartIII-b:C/rep/8/2/pres/3/2/1/5`)

Source of record: `the November 2 reference manuscript`
1219 (the raw lift is smooth through the axis for positive time), 1305-1322, 2548-2551.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`liftPExt`**: along the sequence, `p_lift(τ)` agrees off the axis with a `C^∞` function on
`ℝ³` (source 1219, 1305-1322, 2548-2551). -/
theorem liftPExt (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.LiftPExt := by
  obtain ⟨ν₀, hν₀, H⟩ :=
    UnforcedLeray.Short.IIb.ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth
  filter_upwards [D.pf2_eventually_regime hst hν₀] with n ⟨hν_lt, hR_ge⟩
  intro τ
  set L := D.level n
  obtain ⟨_U, Pw, _hU, hPw, _hper, _hdiv, hoff⟩ :=
    H L.ν ⟨L.ν_pos, hν_lt⟩
      (UnforcedLeray.Short.IIb.trainStream (L.params D.Pl))
      (UnforcedLeray.Short.IIb.trainPressure (L.params D.Pl))
      (pf2_exactPlanarTrain D.Pl L)
      L.ε⁻¹ hR_ge
  refine ⟨fun y => (Pw (τ, y)).re, ?_, ?_⟩
  · exact Complex.reCLM.contDiff.comp (hPw.comp (contDiff_const.prodMk contDiff_id))
  · intro y hy
    have hϱ : UnforcedLeray.Axi.ϱ y ≠ 0 := UnforcedLeray.Axi.ϱ_ne_zero hy
    have hP := (hoff (τ, y) hϱ).2
    dsimp only at hP ⊢
    rw [hP, Complex.ofReal_re, liftPSim L τ y hy]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
