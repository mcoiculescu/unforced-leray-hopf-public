import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSolenoidal
import UnforcedLeray.Units.B0414.Orthogonal

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.B0005 UnforcedLeray.B0281 UnforcedLeray.B0412
open UnforcedLeray.B0414 UnforcedLeray.B0276 UnforcedLeray.B0449
open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.RieszLp

local instance fact_q0_ge_one_corrSol : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  ⟨by norm_num [B0281.q0]⟩

private theorem q0_holder_corrSol : B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
  rw [B0281.q0_eq]
  exact B0276.holderConjugate

private theorem q0_gt_corrSol : 5 / 2 < B0281.q0 := by
  norm_num [B0281.q0]

/-- The selected real correction is distributionally solenoidal at every phase. -/
theorem Params.corr_isSolenoidal (p : Params) (hP1 : p.period ≤ 1)
    (z : p.Z) (τ : ℝ) : IsSolenoidal (p.corr z τ) := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let hLap := hasPhaseOp_nuLapX (p.graphX z)
  let v := phaseRepC (q := q0E) q0E_ne_top hTime (τ : AddCircle p.period)
  have hCorr : (fun y : Space => p.corr z τ y) =ᵐ[volume]
      fun y => realPartVector (v y) := by
    have h1 : (fun y : Space => p.corr z τ y) =ᵐ[volume]
        globalRealChartRep hP1 q0_holder_corrSol q0_gt_corrSol p.ν_pos hTime hLap τ :=
      ae_of_all volume fun y => (p.graph_globalRep_eq_corr hP1 z τ y).symm
    exact h1.trans (globalRealChartRep_ae_phaseRepC hP1 q0_holder_corrSol q0_gt_corrSol
      p.ν_pos hTime hLap τ)
  refine ⟨?_, ?_⟩
  · intro φ hφ
    have hgrad : MemLp (B0005.gvec φ) (conjExp q0E) volume :=
      B0005.memLp_gvec hφ (conjExp q0E)
    have hprod : MemLp (fun y => dotL (B0005.gvec φ y) (v y)) 1 volume :=
      dotL.memLp_of_bilin 1 hgrad (Lp.memLp v)
    have hcomplex : Integrable (fun y => dotL (B0005.gvec φ y) (v y)) :=
      memLp_one_iff_integrable.mp hprod
    have hreal : Integrable (fun y =>
        ∑ i : Fin 3, (realPartVector (v y)) i * spatialTestDerivative i φ y) := by
      refine (hcomplex.re).congr ?_
      filter_upwards with y
      simp [realPartVector, B0005.gvec, dotL_apply, Pi.single_apply,
        Complex.re_sum, Complex.mul_re]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hactual : Integrable (fun y =>
        ∑ i : Fin 3, (p.corr z τ y) i * spatialTestDerivative i φ y) := by
      refine hreal.congr ?_
      filter_upwards [hCorr] with y hy
      simp [hy]
    exact hactual
  · intro φ hφ
    have hgrad : MemLp (B0005.gvec φ) (conjExp q0E) volume :=
      B0005.memLp_gvec hφ (conjExp q0E)
    have hprod : MemLp (fun y => dotL (B0005.gvec φ y) (v y)) 1 volume :=
      dotL.memLp_of_bilin 1 hgrad (Lp.memLp v)
    have hcomplex : Integrable (fun y => dotL (B0005.gvec φ y) (v y)) :=
      memLp_one_iff_integrable.mp hprod
    have hrealEq : (fun y =>
        ∑ i : Fin 3, (realPartVector (v y)) i * spatialTestDerivative i φ y) =ᵐ[volume]
        fun y => (dotL (B0005.gvec φ y) (v y)).re := by
      filter_upwards with y
      simp [realPartVector, B0005.gvec, dotL_apply, Pi.single_apply,
        Complex.re_sum, Complex.mul_re, mul_comm]
    have hdiv := p.phaseRepC_divergence_pairing z τ φ hφ
    have hdiv' : ∫ y, dotL (B0005.gvec φ y) (v y) = 0 := by
      simpa [v] using hdiv
    have hrealZero : ∫ y, (dotL (B0005.gvec φ y) (v y)).re = 0 := by
      calc
        _ = (∫ y, dotL (B0005.gvec φ y) (v y)).re := integral_re hcomplex
        _ = 0 := by rw [hdiv']; rfl
    have hrealIntegral : ∫ y,
        ∑ i : Fin 3, (realPartVector (v y)) i * spatialTestDerivative i φ y = 0 := by
      rw [integral_congr_ae hrealEq]
      exact hrealZero
    have hactualEq : (fun y =>
        ∑ i : Fin 3, (p.corr z τ y) i * spatialTestDerivative i φ y) =ᵐ[volume]
        fun y => ∑ i : Fin 3,
          (realPartVector (v y)) i * spatialTestDerivative i φ y := by
      filter_upwards [hCorr] with y hy
      simp [hy]
    rw [integral_congr_ae hactualEq]
    exact hrealIntegral

end UnforcedLeray.Cons.C03.Concrete
