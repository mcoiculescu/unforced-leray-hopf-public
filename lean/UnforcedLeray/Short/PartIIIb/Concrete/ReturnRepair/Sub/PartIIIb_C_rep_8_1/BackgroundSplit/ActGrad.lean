import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad.Regime
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# `PartIII-b:C/rep/8/1/5/1`: the actual thin-response gradient bound `ActGrad`

Source `the November 2 reference manuscript` 5214-5217 (`repair:phase-gradient`)
and 5282-5289: "The general thin-source estimate is `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`.
Hölder and `R^{-1}=ε` give the exponent `1+3/11+57/22=85/22`."

`SeqData.ActGrad` (`Sub/PartIII-b_C_rep_8_1_5.lean`) asks for the `Y_{22/3}` (ring-chart) bound
`P_ν ε^{57/22} N₁` of the jet density `|DY₁| + |DX₁| + |D²X₁|` of the actual Ward response
`(X₁, Y₁)` of the old thin source `χ_oT₁`.  The proof (helper folder `ActGrad/`):

* the old thin source is a separated source with `L¹` size `∫‖S(·,z)‖_{L²_τ}dz ≤ πR²N₁`
  (`ag_thinSrc`), so the separated estimates are used with `p = 1`, `b = q = 22/3`: the gradient
  kernel has `L^{22/3}` norm `C D^{-101/22}` (`ag_sepDom_lq`, `ag_vert_lq`; source 5203-5205);
* the pointwise leaves of `repair:phase-gradient` (`wgxPointwise`, `wgyPointwise`) and the
  Hessian of the stream cutoff (`ag_hess`, from `streamCutHess`) dominate the meridional jet
  density by one normalized majorant (`ag_core`), whose separated pieces are rotation invariant
  (`ag_sepDom_merid`);
* `(R√ν)^{-101/22} R² ≤ ν^{-3}ε^{57/22}` (`R = ε⁻¹`, `ag_scale_le`) and
  `actJetChartTransfer` give `ActGradAt` with uniform constants (`ag_main`);
* the eventual regime facts (`ν, ε ≤ 1`, `P ≤ 1`, `μ_n(z)` in the Floquet window) come from
  `SeqData.RepairStanding`, as in `phaseGradient_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The actual thin-response gradient bound** (source 5214-5217, 5282-5289). -/
theorem actGrad (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ActGrad := by
  have hσ : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨C, k, hC⟩ := ag_main D.Pl D.K hst.chiY hst.C0_pos hst.mZ_gt (D.σ₀ / 2)
    ((D.σ₀ + 1 / 4) / 2) hσ
  refine ⟨C, k, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hev3 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ dm ^ 3 / 12 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually_le_const (by have := hst.dm_pos; positivity)
  filter_upwards [hev1, hev2, hev3, hst.actual] with n h1 h2 h3 h4 z hz
  have hP : 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 :=
    UnforcedLeray.Short.IIIa.period_le_one_of_small h4.regime h3
  exact hC (D.level n) (D.mu n z) h2.1 h2.2 hP (h1 z hz)

end UnforcedLeray.Short.PartIIIb.Concrete

end
