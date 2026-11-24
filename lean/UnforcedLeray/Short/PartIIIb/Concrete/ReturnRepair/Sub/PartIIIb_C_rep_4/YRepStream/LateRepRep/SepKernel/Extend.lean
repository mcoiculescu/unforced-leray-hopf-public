import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/4`: `FarRepExtend` from the far bridge

Source `the November 2 reference manuscript` 3593-3594 ("we begin with smooth
tensors and then complete in the norms appearing below"), 3905-3912, 5323-5339.

Re-pointed by organizer `ORG:C-review/far-bridge` to the shared completion
`Concrete/ReturnRepair/FarBridge.lean`: the window truncations `1_{W_k}T` converge to `T`
(`FarBridge.tendsto_trunc_win`), their repair sources have the box component sums `1_{W_k}T₂`
(`FarBridge.strSum_repPart_trunc`, `FarBridge.win_box`), the ungained receiver
`htUng ∘ (M_U Sf (0,·))₂` is closed (`FarBridge.RecvClosed.lintegral_comp`: an a.e. subsequence and
Fatou, `htRhoMeasure ≪ gainHTMeasure`), and `phaseL2Lr` of the lifted source does not increase
under truncation (`FarBridge.phaseL2Lr_indicator_le`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem farRepExtend : FarRepExtend := by
  intro Pl K L hC0 Sf A hA T
  have hρ : 0 < L.ρb Pl K := inv_rhoB_pos hC0
  have e : (repPart T).snd = T.snd := by simp [repPart]
  rw [e]
  have hf : Measurable (T.snd : Chart → Ten3) := (Lp.stronglyMeasurable _).measurable
  have hac : htRhoMeasure (cOf L.ν) (L.ρb Pl K) ≪
      gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν :=
    Measure.ae_le_iff_absolutelyContinuous.1 (NearInst.ae_gainHTMeasure _ _ _ _).ge
  have hcl : FarBridge.RecvClosed (fun X : LStr Pl K L =>
      htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L (Sf (repPart X))).snd : Chart → Ten3)) :=
    FarBridge.RecvClosed.lintegral_comp (q := 2) hac two_pos
      (FarBridge.continuous_strSnd.comp ((multOp Pl K L).continuous.comp
        (Sf.continuous.comp (repPart : LStr Pl K L →L[ℝ] LStr Pl K L).continuous)))
  refine FarBridge.le_of_win hρ hcl T hf (fun k => ?_)
  exact (hA (FarBridge.trunc T (FarBridge.win_meas hf k)) _ (FarBridge.win_box hf k)
      (FarBridge.strSum_repPart_trunc hρ T (FarBridge.win_meas hf k))).trans
    (mul_le_mul_of_nonneg_left
      (FarBridge.phaseL2Lr_indicator_le _ _ _ _ (by norm_num) _ _) zero_le)

end UnforcedLeray.Short.PartIIIb.Concrete
