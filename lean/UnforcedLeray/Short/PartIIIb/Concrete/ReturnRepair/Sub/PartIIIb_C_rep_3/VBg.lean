import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Jet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.PresGrad

/-!
# `PartIII-b:C/rep/3/4`: background bounds of `V` and `p_V` (`RepVBg`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5131-5139, 5225-5235, 5245-5247, 5255-5258, 2607-2612, 2641-2642.

State (attempt 3):
* proved unconditionally: the smoothness, `vEtaSup` and measurability clauses
  (`repVBg_contDiffOn`, `repVBg_vEtaSup`, `repVBg_vCoefDens_meas`,
  `repVBg_presChgDens_meas_of_contDiff` in `Sub/PartIII-b_C_rep_3_4.lean`) and the `V ⊗ V` part
  `ε‖|V|²‖_{Y_2} ≤ P_ν` of the thin-coefficient bound (`VBgSq.repVBg_vSq`, `VBg/VSq.lean`, from
  `IIIa.StressCoefficients`);
* reduction: `VBgSq.repVBg_of_jet_presGrad : RepVJetY2 D → RepPresGradY2 D → RepVBg D`
  (`VBg/Leaves.lean`), and `VBgSq.repVBg_of_jet` with the general pressure leaf `RepVPres`.

The target `repVBg` is `VBgSq.repVBg_of_jet_presGrad D hst` applied to proofs of the two leaves
`RepVJetY2 D` (source 5234-5235, 5461-5464, 2347-2387) and `RepPresGradY2 D` (source 5245-5247,
2607-2612, 2641-2642).
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem repVBg (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : RepVBg D :=
  VBgSq.repVBg_of_jet_presGrad D hst (VBgSq.repVJetY2 D hst) (VBgSq.repPresGradY2 D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
