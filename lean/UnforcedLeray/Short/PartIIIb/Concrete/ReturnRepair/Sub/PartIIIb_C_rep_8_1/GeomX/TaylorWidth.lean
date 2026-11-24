import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.FarLeaf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Combine
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge.KernelDict
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge.SigmaCollapse
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge.Newton

/-!
# `PartIII-b:C/rep/8/1/1/1/3`: `taylorWidth`

Source `the November 2 reference manuscript`
lines 5415-5427, 5439-5443, 4764-4791.  Assembles `D.TaylorWidth` from `sepMeanFar`
(`GeomX/TaylorWidth/FarLeaf.lean`), the Newton bridge `newtonBridge kernelDict sigmaCollapse`
(`GeomX/TaylorWidth/Bridge/*.lean`), and `taylorWidthAt_uniform_of`
(`GeomX/TaylorWidth/Combine.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`taylorWidth` from the far-field mean comparison and the Newton bridge**
(source 5415-5427, 5439-5443). -/
theorem taylorWidth_of (hF : SepMeanFar) (hN : TWBridge.NewtonBridge) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.TaylorWidth := by
  obtain ⟨C, k, _, h⟩ := taylorWidthAt_uniform_of hF hN D.Pl D.K hst.C0_pos hst.mZ_gt
  refine ⟨C, k, ?_⟩
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY, retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
    D.coeff_ne] with n hL hνε z hz
  have hLz := hL z hz
  exact h (D.level n) (D.mu n z) hLz.mu_pos (by linarith [hLz.mu_lt]) hνε.1 hνε.2

theorem taylorWidth (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.TaylorWidth :=
  taylorWidth_of sepMeanFar (newtonBridge kernelDict sigmaCollapse) D hst

end UnforcedLeray.Short.PartIIIb.Concrete
