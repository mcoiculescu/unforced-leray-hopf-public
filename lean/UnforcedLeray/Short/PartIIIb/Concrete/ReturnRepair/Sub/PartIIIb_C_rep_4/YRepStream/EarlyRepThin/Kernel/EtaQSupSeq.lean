import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/4/1/org/7/1/8`: `etaQSupSeq`

Source `the November 2 reference manuscript` lines 2713-2721 (fourth line of
`stress-short:coefficients`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem etaQSupSeq (dm dp : ℝ) : EtaQSupSeq dm dp := by
  intro D hst
  obtain ⟨C, k, ν₀, hν₀, h⟩ := UnforcedLeray.Short.IIIa.stressSpacesExactSplit.1 dm dp hst.dm_pos
    D.K.m0 D.K.C0 D.K.k0 hst.m0_pos hst.m0_lt.le D.K.mZ hst.mZ_gt D.Sig D.Pl.eigenvalue
    D.Pl.mode D.Sig_pos hst.planar.eigenpair
  refine ⟨2 * max C 0, k, by positivity, ?_⟩
  filter_upwards [hst.actual, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀),
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with n hn hν he2 s hs
  have hv := (h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.Sin n) (D.V n) (D.rb n)
    hn.split).2.2.2 s hs
  refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : (1 + s) ^ (-3 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h2 : (1 + s) ^ (-1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hε0 : 0 ≤ (D.level n).ε := (D.level n).ε_pos.le
  have h3 : (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ) ≤ 1 :=
    mul_le_one₀ he2.2 (Real.rpow_nonneg (by linarith) _) h2
  have h4 : 0 ≤ (D.level n).ν⁻¹ ^ k := by
    have : 0 < (D.level n).ν := (D.level n).ν_pos
    positivity
  have hC : C ≤ max C 0 := le_max_left C 0
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  calc C * (D.level n).ν⁻¹ ^ k * ((1 + s) ^ (-3 / 4 : ℝ) + (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ))
      ≤ max C 0 * (D.level n).ν⁻¹ ^ k * 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hC h4) (by linarith)
          (by positivity) (by positivity)
    _ = 2 * max C 0 * (D.level n).ν⁻¹ ^ k := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
