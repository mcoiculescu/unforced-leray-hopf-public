import UnforcedLeray.Units.B0449.GraphResolventGlobal
import UnforcedLeray.Lib.PhaseTrace.Trace

/-!
# Phase consistency of the glued B0449 representative

This leaf records exact periodicity from uniqueness of continuous representatives on one central
chart. It also prepares the phase-trace identification boundary.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
variable (e : CVec3)

theorem local_chart_candidates_eqOn_central_period (τ : ℝ)
    (f₀ f₁ : ℝ × Space → ℂ) (hf₀ : Continuous f₀) (hf₁ : Continuous f₁)
    (h₀ : f₀ =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν τ p)))
    (h₁ : f₁ =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν (τ + P) p))) :
    EqOn f₀ f₁ chartCentral := by
  have hperiod : chartJ w ν (τ + P) = chartJ w ν τ := chartJ_add_period w ν τ
  have h₁' : f₁ =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν τ p)) := by
    exact h₁.trans (Filter.Eventually.of_forall fun p => congrArg (dotL e) (congrFun hperiod p))
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq (h₀.trans h₁'.symm)
    isOpen_chartCentral hf₀.continuousOn hf₁.continuousOn

theorem periodic_globalChartRep (y : Space) :
    Function.Periodic (fun τ => globalChartRep hP1 hqq' hq hν hTime hLap e τ y) P := by
  intro τ
  have hEq := local_chart_candidates_eqOn_central_period (w := w) (ν := ν) e τ
    (chosenLocalChart hP1 hqq' hq hν hTime hLap e τ)
    (chosenLocalChart hP1 hqq' hq hν hTime hLap e (τ + P))
    (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e τ)
    (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e (τ + P))
    (chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e τ)
    (chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e (τ + P))
  have hp : (0, (Real.sqrt ν)⁻¹ • y) ∈ chartCentral := by
    simp [chartCentral]
  have hpoint := hEq hp
  change globalChartRep hP1 hqq' hq hν hTime hLap e (τ + P) y =
    globalChartRep hP1 hqq' hq hν hTime hLap e τ y
  exact hpoint.symm

end UnforcedLeray.B0449
