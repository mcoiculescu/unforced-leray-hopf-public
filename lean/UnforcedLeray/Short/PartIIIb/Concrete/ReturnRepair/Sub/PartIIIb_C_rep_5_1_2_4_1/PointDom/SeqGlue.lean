import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `WardYPointDomSeq` from the uniform pointwise statement

Source `the November 2 reference manuscript` 5585-5589 (pointwise domination), 5946
(the window `μ_n(z) = σ₀ + z/(2|log ν_n|)`).  Along the sequence, eventually `ε_n ≤ 1`
(`retNu_retEps_eventually_le_one`), so `R = ε_n⁻¹ ≥ 1`, and `μ_n(z) ≤ 1` (`MuWinLeOne`); the
uniform statement `WardYPointDomUniform` at the cutoff `χ_y` of the standing hypotheses gives the
sequence statement with one `(C, k)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardYPointDomSeq_of (hU : WardYPointDomUniform) (hM : MuWinLeOne) (D : SeqData)
    {dm dp : ℝ} : D.WardYPointDomSeq dm dp := by
  intro hst
  have hχ : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  obtain ⟨C, k, hC⟩ := hU D.K.χy hχ
  refine ⟨C, k, ?_⟩
  have hle := retNu_retEps_eventually_le_one (Pl := D.Pl) (σ₀ := D.σ₀) hst.omega_ne
    hst.gamma_pos D.coeff_ne
  filter_upwards [hle, hM D hst] with n hn hmu z hz
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 1 ≤ (D.level n).ε⁻¹ := (one_le_inv₀ hε).2 hn.2
  exact hC _ _ _ _ _ hR (hmu z hz)

end UnforcedLeray.Short.PartIIIb.Concrete

end
