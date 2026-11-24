import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyFirstOrderLocal.CutRepIBP

/-!
# `FlatBodyFirstOrderLocal` (`PartII-a:N05/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 1684-1689, 1794-1799.

Proves `FlatBodyFirstOrderLocal` by combining:
1. `N05_2_1Aux.flat_body_energy_weak_and_gradBound` (`GradBound.lean`), which provides an
   energy-class representative `(w_rep, Gr)` for `T0flat hc ν μ b` with explicit weighted gradient
   bound `ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal (C_G * Gamma^2 * ‖b‖)`;
2. `N05_2_1Aux.flatCutSpatialDeriv` (`CutRepIBP.lean`), which constructs the concrete
   box-supported `c`-periodic weak `(q, η)` derivatives `dq, deta` of `u = flatStressCutRep c χ W`
   on `cellMeasure c`, establishes their `L²(cellMeasure c)` bounds, and proves the `(q, η)`
   integration-by-parts identities against every `IsMeridTest c φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_2Aux N05_4Aux N05_2_1Aux

/-- **Leaf 1 (`PartII-a:N05/2/1`) — local `(q, η)` first-order energy bound for `χ T_0 b`**. -/
theorem flatBodyFirstOrderLocal : UnforcedLeray.Short.PartIIa.FlatBodyFirstOrderLocal := by
  obtain ⟨C_G, hCG, hGrad⟩ := flat_body_energy_weak_and_gradBound
  refine ⟨4, 2 * C_G + 3, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ _hχ1 hm B hB μ hμM hμγ b
  obtain ⟨w_rep, Gr, hw_rep, hE, hCal, _hWeak⟩ :=
    hGrad ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ μ hμM hμγ b
  let W : HSpace c MeridC := T0flat hc ν μ b
  let u : Profile → MeridC := flatStressCutRep c χ W
  let dq : Profile → MeridC := flatCutSpatialDeriv c χ W Gr 0
  let deta : Profile → MeridC := flatCutSpatialDeriv c χ W Gr 1
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
  set B_Gr : ℝ := C_G * Gam ^ 2 * ‖b‖
  have hB0 : 0 ≤ B_Gr := by dsimp [B_Gr]; positivity
  refine ⟨u, dq, deta,
    flatStressCutRep_ae_eq hc χ hm hB W,
    flatStressCutRep_periodic hc hχ W,
    qPeriodic_flatCutSpatialDeriv hc hχ W Gr 0,
    qPeriodic_flatCutSpatialDeriv hc hχ W Gr 1,
    flatStressCutRep_support hχ W,
    flatCutSpatialDeriv_support hχ W Gr 0,
    flatCutSpatialDeriv_support hχ W Gr 1,
    memLp_flatStressCutRep hc hσ hσH hχ hm W,
    memLp_flatCutSpatialDeriv hc hσ hσH hχ hm W hE.gradMeasurable hB0 hCal 0,
    memLp_flatCutSpatialDeriv hc hσ hσH hχ hm W hE.gradMeasurable hB0 hCal 1,
    fun φ hφ => flatCutSpatialDeriv_ibp hc hσ hσH hχ hm hw_rep hE hB0 hCal 0 hφ,
    fun φ hφ => flatCutSpatialDeriv_ibp hc hσ hσH hχ hm hw_rep hE hB0 hCal 1 hφ,
    ?_⟩
  have hu_le : cellL2Norm c u ≤ Gam ^ 4 * ‖b‖ := by
    calc cellL2Norm c u
        ≤ Gam ^ 3 * ‖b‖ :=
          cellL2Norm_flatStressCutRep_T0flat_le χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ b
      _ ≤ Gam ^ 4 * ‖b‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hG1 (by omega)) (norm_nonneg b)
  have hdq_le : cellL2Norm c dq ≤ (C_G + 1) * Gam ^ 4 * ‖b‖ :=
    cellL2Norm_flatCutSpatialDeriv_T0flat_le χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ b
      hE.gradMeasurable hCG hCal 0
  have hdeta_le : cellL2Norm c deta ≤ (C_G + 1) * Gam ^ 4 * ‖b‖ :=
    cellL2Norm_flatCutSpatialDeriv_T0flat_le χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ b
      hE.gradMeasurable hCG hCal 1
  linarith

end UnforcedLeray.Short.PartIIa
