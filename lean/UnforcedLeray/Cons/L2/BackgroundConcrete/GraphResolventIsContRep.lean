import UnforcedLeray.Units.B0449.GraphResolventRepresentative
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# Transfer the B0449 graph representative to the Background continuous-representative API

This consumer leaf is deliberately downstream of the B0449 construction. It identifies the
source-facing continuous field with the selected jointly measurable representative only in the
product-a.e. sense required by `IsContRep`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0449

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)

local notation "qE" => ENNReal.ofReal qR

/-- The source-facing B0449 field is a continuous representative of the real part of the graph
element in the existing Background API. -/
theorem graph_globalRealChartRep_isContRep :
    IsContRep w (fun τ y =>
      globalRealChartRep hP1 hqq' hq hν hTime hLap τ y) := by
  have hqtop : qE ≠ ⊤ := ENNReal.ofReal_ne_top
  have hphaseLine := PhaseTrace.phaseRep_ae_line hqtop hTime
  have hslice : ∀ᵐ τ : ℝ ∂volume,
      (fun y => globalRealChartRep hP1 hqq' hq hν hTime hLap τ y) =ᵐ[volume]
        (fun y => reP (rep w τ y)) := by
    filter_upwards [hphaseLine] with τ hτ
    have hphaseEq : phaseRepC (q := qE) hqtop hTime (τ : AddCircle P) =
        w (τ : AddCircle P) := by
      rw [phaseRepC_coe]
      exact hτ
    have hphaseFn : (phaseRepC (q := qE) hqtop hTime (τ : AddCircle P) :
        Space → CVec3) =ᵐ[volume] fun y => rep w τ y := by
      exact (Lp.ext_iff.mp hphaseEq).trans (rep_slice w τ).symm
    have hreal := globalRealChartRep_ae_phaseRepC hP1 hqq' hq hν hTime hLap τ
    filter_upwards [hreal, hphaseFn] with y hy hy'
    simpa [realPartVector, reP] using hy.trans (congrArg realPartVector hy')
  let F : ℝ × Space → Space := fun p =>
    globalRealChartRep hP1 hqq' hq hν hTime hLap p.1 p.2
  let G : ℝ × Space → Space := fun p => reP (rep w p.1 p.2)
  have hF : Continuous F := by
    exact continuous_globalRealChartRep hP1 hqq' hq hν hTime hLap
  have hReP : Continuous (fun v : CVec3 => reP v) := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      (continuous_pi fun i => Complex.continuous_re.comp
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℂ) i))
  have hG : StronglyMeasurable G := by
    change StronglyMeasurable (fun p : ℝ × Space => reP (rep w p.1 p.2))
    exact hReP.comp_stronglyMeasurable (stronglyMeasurable_rep w)
  have hset : MeasurableSet {p : ℝ × Space | F p = G p} :=
    measurableSet_eq_fun hF.measurable hG.measurable
  have hprod : ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure Space), F p = G p :=
    (Measure.ae_prod_iff_ae_ae hset).2 hslice
  refine ⟨hF, ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure Space), F p = G p
  exact hprod

end UnforcedLeray.Cons.C03.Concrete
