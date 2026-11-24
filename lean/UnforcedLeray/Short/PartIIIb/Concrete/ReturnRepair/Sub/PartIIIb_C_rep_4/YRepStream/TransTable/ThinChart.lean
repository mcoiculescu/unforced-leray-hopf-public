import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart.Core3
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.SplitMult
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_2
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_3
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_9

/-!
# `PartIII-b:C/rep/4/4/1/org/3/2`: thin multiplication on the transition window

Source `the November 2 reference manuscript` 2697 (`Z₁`), 2706 (`v = s^{-1/2}V`),
2717-2723 (`V_m(s) = ‖Wv(s)‖_{L²_ηL^∞_q} ≤ P_ν((1+s)^{-3/4} + ε(1+s)^{-1/4})`), 2666-2668
(`τ = 2q/R + log s`: a `q`-cell is one phase period).

The analytic content is `TC.z1Maj_multMaj_le` (`ThinChart/Core3.lean`, unconditional): Tonelli in
`(s, q, η)`, `L^∞_q` of the coefficient against the cell `L²_q` norm `c‖f(·,y)‖²_{L²_τ}`
(`TC.qint`), the window `4/(5ν) ≤ s ≤ 1/ν` of the annulus.  Its coefficient input is the fourth
clause of `IIIa.StressCoefficients` (the open leaf, source 2703-2723), instantiated at the level
exactly as in `NearInst.splitMultBound_of`/`seq_splitMult`.  Hence `thinChart_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Thin multiplication on the transition window**, from the stress coefficients of `IIIa`
(`IIIa.StressCoefficients`, source 2703-2723). -/
theorem thinChart_of (hSC : UnforcedLeray.Short.IIIa.StressCoefficients) (dm dp : ℝ) :
    ThinChart dm dp := by
  intro D hst
  obtain ⟨C, k, ν₀, hν₀, h⟩ := hSC dm dp hst.dm_pos D.K.m0 D.K.C0 D.K.k0 hst.m0_pos
    hst.m0_lt.le D.K.mZ hst.mZ_gt D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos hst.planar.eigenpair
  obtain ⟨C', k', ν₀', hν₀', h'⟩ := NearInst.splitMultBound_of hSC dm dp hst.dm_pos D.K.m0 D.K.C0
    D.K.k0 hst.m0_pos hst.m0_lt.le hst.C0_pos D.K.mZ hst.mZ_gt D.Sig D.Pl.eigenvalue D.Pl.mode
    D.Sig_pos hst.planar.eigenpair
  refine ⟨2 * (|C| + 1), k + 1, by positivity, ?_⟩
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hst.actual, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀),
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀'), hev2]
    with n hn hν hν' e2 f A hf hvan hA
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν0
  have hv := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.Sin n) (D.V n) (D.rb n) hn.split
  have hm := (h' ((D.level n).params D.Pl) _ hn.regime hν' rfl rfl (D.Sin n) (D.V n) (D.rb n)
    hn.split).1
  have hP : 2 * (D.level n).ε * cOf (D.level n).ν = 2 * cOf (D.level n).ν / (D.level n).ε⁻¹ := by
    field_simp
  rw [hP] at hf hA
  have hB : (0 : ℝ) < 2 * (|C| + 1) * (D.level n).ν⁻¹ ^ k := by positivity
  have hVb : ∀ s : ℝ, 0 < s → IIIa.etaL2QSup (cOf (D.level n).ν) D.K.mZ
      (IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) s ≤
      ENNReal.ofReal (2 * (|C| + 1) * (D.level n).ν⁻¹ ^ k) := by
    intro s hs
    refine (hv.2.2.2 s hs).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (1 + s) ^ (-3 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h2 : (1 + s) ^ (-1 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h3 : (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ) ≤ 1 :=
      mul_le_one₀ e2.2 (Real.rpow_nonneg (by linarith) _ ) h2
    have h4 : 0 ≤ (D.level n).ν⁻¹ ^ k := by positivity
    calc C * (D.level n).ν⁻¹ ^ k * ((1 + s) ^ (-3 / 4 : ℝ) + (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ))
        ≤ |C| * (D.level n).ν⁻¹ ^ k * 2 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) h4) (by linarith)
            (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [abs_nonneg C]
  have key := TC.z1Maj_multMaj_le (mZ := D.K.mZ) hR hc hν0 e2.1 hB hm hVb hf hvan A hA
  refine key.trans (le_of_eq ?_)
  congr 2
  rw [pow_succ]; ring

theorem thinChart (dm dp : ℝ) : ThinChart dm dp :=
  thinChart_of
    (UnforcedLeray.Short.IIIa.stressCoefficients_of
      UnforcedLeray.Short.IIIa.rawCoeffLate
      UnforcedLeray.Short.IIIa.rawCoeffEarly
      UnforcedLeray.Short.IIIa.inletCoeffBounds) dm dp

end UnforcedLeray.Short.PartIIIb.Concrete

end
