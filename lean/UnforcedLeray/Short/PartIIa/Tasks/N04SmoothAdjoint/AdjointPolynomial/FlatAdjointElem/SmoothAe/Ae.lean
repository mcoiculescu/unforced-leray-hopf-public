import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2_1
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.FlatAdjointWeakEq
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.CausalOperator

/-!
# Sub `PartII-a_N04_2_2_1`, conjunct `AeProp` (source lines 1803-1808)

`(T0flat hc ν μ).adjoint Z = adjoint R0 (PepsC 0 c Z)`, the Bochner integral
`∫_{t>0} lapT0adj W t` represents `adjoint R0 W`, and the a.e. evaluation of that integral is
`causalAdjointRep (thetaWeight 0)`, which is `flatAdjointRep` by `causalAdjointRep_thetaWeight_zero`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N04_2_2_1

open UnforcedLeray.Short.PartIIa UnforcedLeray.Short.PartIIa.FlatAdjointElemAux
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225
  UnforcedLeray.B0226

/-- Inner product with a fixed vector commutes with a Bochner integral in the first slot. -/
theorem inner_integral_left_ae {c : ℝ} {f : ℝ → HSpace c MeridC}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (W : HSpace c MeridC) :
    inner ℂ (∫ t in Ioi (0 : ℝ), f t) W = ∫ t in Ioi (0 : ℝ), inner ℂ (f t) W := by
  rw [← inner_conj_symm (∫ t in Ioi (0 : ℝ), f t) W, ← integral_inner hf W, ← integral_conj]
  simp only [inner_conj_symm]

/-- The adjoint of `R0` is the Laplace integral of the adjoint semigroup (weight `thetaWeight 0 = 1`). -/
theorem adjoint_R0_apply_integral {c ν : ℝ} (hc : 0 < c) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (W : HSpace c MeridC) :
    ContinuousLinearMap.adjoint (B0225.R0 hc ν μ : HSpace c MeridC →L[ℂ] HSpace c MeridC) W =
      ∫ t in Ioi (0 : ℝ), lapT0adj hc ν μ (thetaWeight 0) W t := by
  have hβ1 : ∀ t : ℝ, thetaWeight 0 t = 1 := fun t => congrFun thetaWeight_zero t
  refine ext_inner_left ℂ fun v => ?_
  have hR : B0225.R0 hc ν μ v = ∫ t in Ioi (0 : ℝ), lapT0 hc ν μ v t :=
    B0225.R0_apply hc ν hμ v
  rw [ContinuousLinearMap.adjoint_inner_right, hR,
    inner_integral_left_ae (integrableOn_lapT0 hc ν hμ v) W,
    ← integral_inner (integrableOn_lapT0adj hc ν hμ (continuous_thetaWeight 0)
      (norm_thetaWeight_le 0) W) v]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  have hA : inner ℂ (B0224.T0 hc ν t v) W = inner ℂ v (B0224.T0adj hc ν t W) := by
    have hc1 := UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.t0_complex_adjoint
      c ν hc t W v
    calc inner ℂ (B0224.T0 hc ν t v) W
        = starRingEnd ℂ (inner ℂ W (B0224.T0 hc ν t v)) := (inner_conj_symm _ _).symm
      _ = starRingEnd ℂ (inner ℂ (B0224.T0adj hc ν t W) v) := by rw [hc1]
      _ = inner ℂ v (B0224.T0adj hc ν t W) := inner_conj_symm _ _
  have hexp : starRingEnd ℂ (Complex.exp (-(μ * t))) =
      Complex.exp (-(starRingEnd ℂ μ * t)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  simp only [lapT0, lapT0adj, hβ1, mul_one]
  rw [inner_smul_left, inner_smul_right, hA, hexp]

/-- **Adjoint identification for `P_0` and `T_0`.** -/
theorem flatAdjointAeProp : UnforcedLeray.Short.PartIIa.N04_2_2_1.AeProp := by
  intro ν c σ H1 γs hc hν hσ hσH1 hγs μ hμ Z h hh hZ
  have hμpos : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hμ
  have hTeq : (T0flat hc ν μ : HSpace c MeridC →L[ℂ] HSpace c MeridC) =
      PepsC 0 c ∘L B0225.R0 hc ν μ := by
    refine ContinuousLinearMap.ext fun x => ?_
    exact T0flat_eq_PepsC_comp_R0 hc hμpos x
  have hadj : ContinuousLinearMap.adjoint (T0flat hc ν μ) Z =
      ContinuousLinearMap.adjoint (B0225.R0 hc ν μ : HSpace c MeridC →L[ℂ] HSpace c MeridC)
        (PepsC 0 c Z) := by
    rw [hTeq, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, adjoint_PepsC]
  have hae := integral_lapT0adj_ae_eq hc ν hμpos (continuous_thetaWeight 0)
    (norm_thetaWeight_le 0) (PepsC 0 c Z) hh.smooth.continuous.stronglyMeasurable
    hh.periodic hZ
  rw [causalAdjointRep_thetaWeight_zero] at hae
  rw [hadj, adjoint_R0_apply_integral hc hμpos]
  exact hae

end UnforcedLeray.Short.PartIIa.N04_2_2_1
