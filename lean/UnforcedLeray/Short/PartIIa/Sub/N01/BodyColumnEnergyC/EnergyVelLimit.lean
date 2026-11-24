import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_4
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.VelFAeTransfer
import UnforcedLeray.Units.B0225.Laplace

/-!
# `PartII-a:N01/9/1/4/2`: `energyVelLimit`

Source `the November 2 reference manuscript`
lines 3426-3430, 1684-1689. The chart transport `cellPtInv` carries `ageμ c (-3/2)` to
`c⁻¹ • measureH c` (`CellPtInvH`), so the `L²(ageμ c (-3/2))` energy of `velF c f` is `c⁻¹ ‖f‖²_𝓗`;
together with `‖R₀(μ)‖ ≤ (Re μ + 1/4)⁻¹` this gives the convergence `b_k → velF c (R₀ g)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.EnergyVelLimitAux

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv cpcInvH_eq)
open UnforcedLeray.Short.IIIa (vnorm2)

lemma vnorm2_sq (v : MeridC) : vnorm2 (fun i => v i) ^ 2 = ‖v‖ ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), EuclideanSpace.norm_sq_eq]

lemma lint_Hnorm (c : ℝ) (h : HSpace c MeridC) :
    ∫⁻ y, ENNReal.ofReal (‖h y‖ ^ 2) ∂(measureH c) = ENNReal.ofReal (‖h‖ ^ 2) := by
  have h1 : ∀ y, ENNReal.ofReal (‖h y‖ ^ 2) = ‖h y‖ₑ ^ (2 : ℝ) := fun y => by
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [h1]
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (μ := measureH c) (f := h) (p := 2) (by norm_num)
  have h3 : (∫⁻ y, ‖h y‖ₑ ^ (2 : ℝ) ∂(measureH c)) = eLpNorm h 2 (measureH c) ^ (2 : ℕ) := by
    simpa [ENNReal.rpow_two] using h2.symm
  rw [h3, ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top h).ne]

lemma lint_transport (c : ℝ) (hc : 0 < c) (F : Profile → MeridC)
    (hF : AEStronglyMeasurable F (measureH c)) :
    ∫⁻ x, ENNReal.ofReal (vnorm2 (fun i => F (cellPtInv c x) i) ^ 2) ∂(ageμ c (-3 / 2)) =
      ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2) ∂(measureH c) := by
  have hmap := cpcInvH_eq c hc
  have hm := measurable_cellPtInv c
  have hae : AEMeasurable (fun y => ENNReal.ofReal (‖F y‖ ^ 2))
      (Measure.map (cellPtInv c) (ageμ c (-3 / 2))) := by
    rw [hmap]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hF.norm.aemeasurable.pow_const 2)).smul_measure _
  have := lintegral_map' hae hm.aemeasurable
  simp_rw [vnorm2_sq]
  rw [← this, hmap, lintegral_smul_measure, smul_eq_mul]

end UnforcedLeray.Short.PartIIa.N01.EnergyVelLimitAux

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv)
open UnforcedLeray.Short.IIIa (vnorm2)
open EnergyVelLimitAux

theorem energyVelLimit : EnergyVelLimit := by
  intro c ν hc hν μ hμ g gk hg bk hbk hbm
  set U : HSpace c MeridC := (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) with hU
  set u' : Profile → MeridC := (Lp.aestronglyMeasurable U).mk U with hu'
  have hu'm : StronglyMeasurable u' := (Lp.aestronglyMeasurable U).stronglyMeasurable_mk
  have hu'ae : U =ᵐ[measureH c] u' := (Lp.aestronglyMeasurable U).ae_eq_mk
  have hUnorm : ∫⁻ y, ENNReal.ofReal (‖u' y‖ ^ 2) ∂(measureH c) = ENNReal.ofReal (‖U‖ ^ 2) := by
    rw [← lint_Hnorm c U]
    refine lintegral_congr_ae ?_
    filter_upwards [hu'ae] with y hy
    rw [hy]
  refine ⟨fun x i => u' (cellPtInv c x) i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).continuous.measurable.comp
      (hu'm.measurable.comp (measurable_cellPtInv c)))
  · exact velFAeTransfer c hc u' _ hu'ae.symm
  · have key : ∀ k, ∫⁻ p, ENNReal.ofReal (vnorm2 (fun i => bk k p i - u' (cellPtInv c p) i) ^ 2)
        ∂(ageμ c (-3 / 2)) = ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (‖UnforcedLeray.B0225.R0 hc ν μ (gk k - g)‖ ^ 2) := by
      intro k
      set uk : HSpace c MeridC := (UnforcedLeray.B0225.R0 hc ν μ (gk k) : HSpace c MeridC) with huk
      have h1 : ∫⁻ p, ENNReal.ofReal (vnorm2 (fun i => bk k p i - u' (cellPtInv c p) i) ^ 2)
          ∂(ageμ c (-3 / 2)) = ∫⁻ p, ENNReal.ofReal
            (vnorm2 (fun i => (fun y => uk y - u' y) (cellPtInv c p) i) ^ 2) ∂(ageμ c (-3 / 2)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hbk k] with x hx
        have : (fun i => bk k x i - u' (cellPtInv c x) i) =
            fun i => (fun y => uk y - u' y) (cellPtInv c x) i := by
          funext i
          rw [hx]
          rfl
        rw [this]
      rw [h1]
      refine (lint_transport c hc (fun y => uk y - u' y)
        ((Lp.aestronglyMeasurable uk).sub hu'm.aestronglyMeasurable)).trans ?_
      congr 1
      have h2 : ∫⁻ y, ENNReal.ofReal (‖uk y - u' y‖ ^ 2) ∂(measureH c) =
          ∫⁻ y, ENNReal.ofReal (‖(uk - U) y‖ ^ 2) ∂(measureH c) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hu'ae, Lp.coeFn_sub uk U] with y hy1 hy2
        rw [hy2, Pi.sub_apply, hy1]
      rw [h2, lint_Hnorm c (uk - U)]
      congr 3
      rw [huk, hU, ← map_sub]
    simp_rw [key]
    have hnorm : Tendsto (fun k => ‖gk k - g‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hg
    have hop : ‖(UnforcedLeray.B0225.R0 hc ν μ : HSpace c MeridC →L[ℂ] HSpace c MeridC)‖ ≤
        (μ.re + 1 / 4)⁻¹ := UnforcedLeray.B0225.norm_R0_le hc ν hμ
    have hbd : ∀ k, ‖UnforcedLeray.B0225.R0 hc ν μ (gk k - g)‖ ≤
        (μ.re + 1 / 4)⁻¹ * ‖gk k - g‖ := fun k =>
      (ContinuousLinearMap.le_of_opNorm_le _ hop (gk k - g) :)
    have h0 : Tendsto (fun k => ‖UnforcedLeray.B0225.R0 hc ν μ (gk k - g)‖) atTop (𝓝 0) :=
      squeeze_zero (fun k => norm_nonneg _) hbd (by simpa using hnorm.const_mul (μ.re + 1 / 4)⁻¹)
    have h3 : Tendsto (fun k => c⁻¹ * ‖UnforcedLeray.B0225.R0 hc ν μ (gk k - g)‖ ^ 2)
        atTop (𝓝 0) := by
      simpa using (h0.pow 2).const_mul c⁻¹
    have h4 := ENNReal.tendsto_ofReal h3
    simp only [ENNReal.ofReal_zero] at h4
    refine h4.congr fun k => ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  · rw [lint_transport c hc u' hu'm.aestronglyMeasurable, hUnorm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end UnforcedLeray.Short.PartIIa.N01
