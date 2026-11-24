import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateL4
import UnforcedLeray.Lib.LerayC.IsometryC
import UnforcedLeray.Lib.AxisymmetricB.Unitary

/-!
# All-phase symmetry of the actual graph correction

The stored graph element is invariant only as an Lq phase-space class. This leaf first transfers
that invariance to every slice of its continuous phase trace, then to the real continuous spatial
representative of the actual correction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.B0412 UnforcedLeray.B0276 UnforcedLeray.B0449
open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.RieszLp

local instance fact_q0_ge_one_symmetry : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  ⟨by norm_num [B0281.q0]⟩

private theorem q0_holder : B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
  rw [B0281.q0_eq]
  exact B0276.holderConjugate

private theorem q0_gt : 5 / 2 < B0281.q0 := by norm_num [B0281.q0]

private theorem reV_gC (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) :
    reV (B0412.gC g v) = g (reV v) := by
  ext i
  change (B0412.gC g v i).re = (g (reV v)) i
  rw [B0412.gC_apply]
  have hx : reV v = ∑ j : Fin 3, (reV v) j • EuclideanSpace.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [reV_apply, B0412.gEntry, Complex.re_sum, Complex.mul_re,
    map_smul, Pi.single_apply, mul_comm]

/-- The continuous phase trace of an O-invariant graph element is O-invariant at every phase. -/
theorem Params.phaseRepC_spatialAct_eq (p : Params) (z : p.Z)
    (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (τ : ℝ) :
    B0412.spatialAct q0E g
      (phaseRepC (q := q0E) q0E_ne_top (hasPhaseOp_T0X (p.graphX z))
        (τ : AddCircle p.period)) =
      phaseRepC (q := q0E) q0E_ne_top (hasPhaseOp_T0X (p.graphX z))
        (τ : AddCircle p.period) := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let w := p.wOf z
  have hO : IsOInvariant w := by
    have hwX : w ∈ X p.period p.ν q0E := (p.graphX z).property
    rcases (mem_X.mp hwX) with ⟨_, _, _, hO⟩
    exact hO
  have hgood := (isOInvariant_iff w).1 hO g hg
  have htrace := phaseRepC_ae q0E_ne_top hTime
  let A : AddCircle p.period → Lp CVec3 q0E (volume : Measure Space) :=
    fun θ => B0412.spatialAct q0E g (phaseRepC (q := q0E) q0E_ne_top hTime θ) -
      phaseRepC (q := q0E) q0E_ne_top hTime θ
  have hAcont : Continuous A := by
    dsimp [A]
    exact ((B0412.spatialAct q0E g).continuous.comp
      (phaseRepC (q := q0E) q0E_ne_top hTime).continuous).sub
        (phaseRepC (q := q0E) q0E_ne_top hTime).continuous
  have hAae : A =ᵐ[AddCircle.haarAddCircle] (fun _ => 0) := by
    filter_upwards [hgood, htrace] with θ hθ hθtrace
    have hθtrace' : w θ = phaseRepC (q := q0E) q0E_ne_top hTime θ := by
      simpa [w, Params.graphX] using hθtrace
    have hspatial : B0412.spatialAct q0E g (w θ) = w θ :=
      (B0412.spatialAct_eq_iff g (w θ)).2 hθ
    have htraceInv : B0412.spatialAct q0E g
        (phaseRepC (q := q0E) q0E_ne_top hTime θ) =
        phaseRepC (q := q0E) q0E_ne_top hTime θ := by
      calc
        _ = B0412.spatialAct q0E g (w θ) := by rw [← hθtrace']
        _ = w θ := hspatial
        _ = _ := hθtrace'
    simp [A, htraceInv]
  have hAeq : A = fun _ => (0 : Lp CVec3 q0E (volume : Measure Space)) :=
    (Continuous.ae_eq_iff_eq (AddCircle.haarAddCircle (T := p.period))
      hAcont continuous_const).mp hAae
  have hzero := congrFun hAeq (τ : AddCircle p.period)
  dsimp [A] at hzero
  exact sub_eq_zero.mp hzero

/-- Every slice of the source-facing selected correction is axisymmetric without swirl. -/
theorem Params.corr_isAxisymmetricNoSwirl (p : Params) (hP1 : p.period ≤ 1)
    (z : p.Z) (τ : ℝ) : IsAxisymmetricNoSwirl (p.corr z τ) := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let hLap := hasPhaseOp_nuLapX (p.graphX z)
  let v := phaseRepC (q := q0E) q0E_ne_top hTime (τ : AddCircle p.period)
  have hCorr : (fun y : Space => p.corr z τ y) =ᵐ[volume]
      fun y => realPartVector (v y) := by
    have h1 : (fun y : Space => p.corr z τ y) =ᵐ[volume]
        globalRealChartRep hP1 q0_holder q0_gt p.ν_pos hTime hLap τ :=
      ae_of_all volume fun y => (p.graph_globalRep_eq_corr hP1 z τ y).symm
    exact h1.trans (globalRealChartRep_ae_phaseRepC hP1 q0_holder q0_gt p.ν_pos hTime hLap τ)
  intro g hg
  have hact := p.phaseRepC_spatialAct_eq z g hg τ
  have hspatial := (B0412.spatialAct_eq_iff g v).1 hact
  have hcomp := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp hCorr
  filter_upwards [hcomp, hCorr, hspatial] with y h1 h2 h3
  change g (p.corr z τ (g.symm y)) = p.corr z τ y
  change p.corr z τ (g.symm y) = realPartVector (v (g.symm y)) at h1
  change p.corr z τ y = realPartVector (v y) at h2
  rw [h1, h2]
  change g (reV (v (g.symm y))) = reV (v y)
  calc
    g (reV (v (g.symm y))) = reV (B0412.gC g (v (g.symm y))) :=
      (reV_gC g (v (g.symm y))).symm
    _ = reV (v y) := congrArg reV h3

end UnforcedLeray.Cons.C03.Concrete
