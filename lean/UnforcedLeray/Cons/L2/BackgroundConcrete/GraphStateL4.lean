import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphResolventIsContRep
import UnforcedLeray.Units.B0276
import UnforcedLeray.Units.B0449.GraphResolventL4Continuity

/-!
# L4 trace regularity of an actual B0449 graph state

This leaf applies the B0449 graph result to the actual first component of a state in `p.Z`.
The selected `contRep` is identified with the globally continuous chart representative by
uniqueness of continuous representatives, so the L4 statement concerns the source-facing field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.B0412 UnforcedLeray.B0276 UnforcedLeray.B0449
open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

local instance fact_one_le_four_graphStateL4 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_q0_ge_one : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  ⟨by norm_num [B0281.q0]⟩

private theorem q0_holder : B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
  rw [B0281.q0_eq]
  exact B0276.holderConjugate

private theorem q0_gt : 5 / 2 < B0281.q0 := by norm_num [B0281.q0]
private theorem q0_lt_four : B0281.q0 < 4 := by norm_num [B0281.q0]

/-- Recover the actual `X_{q₀}` correction from the graph triple of a state. -/
def Params.graphX (p : Params) (z : p.Z) : X p.period p.ν q0E := by
  have hg := (mem_graphSpace (P := p.period) (ν := p.ν)).1 z.2
  have hx := (mem_XGraph_iff (P := p.period) (ν := p.ν) (q := q0E)).1 hg.1
  exact ⟨p.wOf z, hx.1⟩

/-- The B0449 continuous field and the selected correction representative agree at every phase
and point, by uniqueness of continuous representatives on product space. -/
theorem Params.graph_globalRep_eq_corr (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (τ : ℝ) (y : Space) :
    globalRealChartRep hP1 q0_holder q0_gt p.ν_pos (hasPhaseOp_T0X (p.graphX z))
      (hasPhaseOp_nuLapX (p.graphX z)) τ y = p.corr z τ y := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let hLap := hasPhaseOp_nuLapX (p.graphX z)
  let F : ℝ → SpatialField := globalRealChartRep hP1 q0_holder q0_gt p.ν_pos hTime hLap
  have hF : IsContRep (p.wOf z) F :=
    graph_globalRealChartRep_isContRep hP1 q0_holder q0_gt p.ν_pos hTime hLap
  have hcont : IsContRep (p.wOf z) (p.corr z) := by
    exact contRep_spec ⟨F, hF⟩
  have hAE : (fun x : ℝ × Space => p.corr z x.1 x.2) =ᵐ[volume]
      (fun x => F x.1 x.2) := hcont.2.trans hF.2.symm
  have hEq : (fun x : ℝ × Space => p.corr z x.1 x.2) =
      (fun x => F x.1 x.2) :=
    (Continuous.ae_eq_iff_eq volume hcont.1 hF.1).mp hAE
  exact (congrFun hEq (τ, y)).symm

/-- Every phase slice of the actual correction has the L4 regularity supplied by the graph
resolvent. -/
theorem Params.corr_memLp_four (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) (τ : ℝ) :
    MemLp (p.corr z τ) 4 volume := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let hLap := hasPhaseOp_nuLapX (p.graphX z)
  let F : ℝ → SpatialField := globalRealChartRep hP1 q0_holder q0_gt p.ν_pos hTime hLap
  have hglobal : MemLp (F τ) 4 volume :=
    globalRealChartRep_memLp_four hP1 q0_holder q0_gt p.ν_pos hTime hLap q0_lt_four τ
  have hAE : F τ =ᵐ[volume] p.corr z τ := by
    filter_upwards with y
    exact p.graph_globalRep_eq_corr hP1 z τ y
  exact (memLp_congr_ae hAE).mp hglobal

/-- The L4 path of the actual selected correction representative. -/
def Params.corrL4Path (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) :
    ℝ → Lp Space 4 (volume : Measure Space) :=
  fun τ => (p.corr_memLp_four hP1 z τ).toLp _

/-- The actual selected correction has continuous L4 phase slices. -/
theorem Params.continuous_corrL4Path (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) :
    Continuous (p.corrL4Path hP1 z) := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let hLap := hasPhaseOp_nuLapX (p.graphX z)
  let F : ℝ → SpatialField := globalRealChartRep hP1 q0_holder q0_gt p.ν_pos hTime hLap
  have hEq (τ : ℝ) : p.corrL4Path hP1 z τ =
      globalRealChartRepL4Path hP1 q0_holder q0_gt q0_lt_four p.ν_pos hTime hLap τ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (p.corr_memLp_four hP1 z τ),
      MemLp.coeFn_toLp (globalRealChartRep_memLp_four hP1
        q0_holder q0_gt p.ν_pos hTime hLap q0_lt_four τ)] with y hy hc
    calc
      ((p.corr_memLp_four hP1 z τ).toLp _ : Lp Space 4 volume) y = p.corr z τ y := hy
      _ = F τ y := (p.graph_globalRep_eq_corr hP1 z τ y).symm
      _ = ((globalRealChartRep_memLp_four hP1 q0_holder q0_gt p.ν_pos hTime hLap
          q0_lt_four τ).toLp _) y := hc.symm
  have hpath : Continuous (fun τ => globalRealChartRepL4Path hP1
      q0_holder q0_gt q0_lt_four p.ν_pos hTime hLap τ) :=
    continuous_globalRealChartRepL4Path hP1 q0_holder q0_gt q0_lt_four p.ν_pos hTime hLap
  exact hpath.congr (fun τ => (hEq τ).symm)

end UnforcedLeray.Cons.C03.Concrete
