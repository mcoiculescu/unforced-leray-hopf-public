import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level

/-!
# `PartIII-b:C/rep/5/2/1/5`: `RepFarExt` from the far bridge

Source `the November 2 reference manuscript` 3593-3595 (smooth tensors first, then
completion in the norms), 3905-3912.

Re-pointed by organizer `ORG:C-review/far-bridge` to the shared completion
`Concrete/ReturnRepair/FarBridge.lean` (`FarBridge.le_of_win`): the window truncations of `F`
have the box component sums `1_{W_k}f` (`FarBridge.strSum_trunc_of`, `FarBridge.win_box`), the
receiver `eLpNorm (Sf ·) 2 (srcMeasure c)` is closed (`FarBridge.RecvClosed.eLpNorm_comp`,
`srcMeasure ≪ bodyMeasure`), and `phaseL2Lr` of the lifted source does not increase under
truncation (`FarBridge.phaseL2Lr_indicator_le`).  (The four-lemma route of `RepFarExtOf.lean` is
no longer used.)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem repFarExt : RepFarExt := by
  intro Pl K L μ C hC0 hB Sf hSf F f hf hF
  have hρ : 0 < L.ρb Pl K := inv_rhoB_pos hC0
  have hac : srcMeasure (cOf L.ν) ≪ bodyMeasure (cOf L.ν) (gRate Pl) L.ν :=
    Measure.ae_le_iff_absolutelyContinuous.1
      ((NearInst.ae_srcMeasure _).trans (NearInst.ae_bodyMeasure _ _ _).symm).le
  refine FarBridge.le_of_win hρ
    (Φ := fun X : LStr Pl K L => eLpNorm (Sf X : Chart → Merid) 2 (srcMeasure (cOf L.ν)))
    (FarBridge.RecvClosed.eLpNorm_comp hac two_ne_zero ENNReal.ofNat_ne_top Sf.continuous)
    F hf (fun k => ?_)
  exact (hB Sf hSf _ _ (FarBridge.win_box hf k)
      (FarBridge.strSum_trunc_of hρ F (FarBridge.win_meas hf k) hF)).trans
    (mul_le_mul_of_nonneg_left
      (FarBridge.phaseL2Lr_indicator_le _ _ _ _ (by norm_num) _ _) zero_le)

end UnforcedLeray.Short.PartIIIb.Concrete
