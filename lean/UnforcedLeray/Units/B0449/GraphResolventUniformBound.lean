import UnforcedLeray.Units.B0449.GraphResolventRepresentative
import UnforcedLeray.Lib.HeatR3B.SpaceTime

/-!
# Uniform pointwise bounds for the glued B0449 graph field

The cutoff resolvent gives a uniformly Lq-bounded actual source. Its continuous ST output agrees
with the selected local chart candidate on the central open chart, so the resulting global scalar
representative has a bound independent of its phase.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.Heat

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)

/-- A scalar chart projection has one pointwise bound valid for every phase and spatial point. -/
theorem exists_globalChartRep_uniform_bound (e : CVec3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ y,
      ‖globalChartRep hP1 hqq' hq hν hTime hLap e τ y‖ ≤ M := by
  obtain ⟨C, hCtop, hCuniform⟩ :=
    chartJ_cutoff_FST_uniform_eLpNorm hP1 hq hν (w := w) (a := a) (b := b) e
  let K : ℝ := (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal * C.toReal
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro τ y
  obtain ⟨H, F, hHae, hFae, hHF, ⟨Hc, hHc, hHraw, hHbound⟩, hUniformτ⟩ :=
    chartJ_cutoff_ST_continuous_rep hP1 hqq' hq hν hTime hLap τ e
  let f : ℝ × Space → ℂ := chosenLocalChart hP1 hqq' hq hν hTime hLap e τ
  let B : ℝ × Space → ℂ := fun p => Hc (productToST p)
  have hBcont : Continuous B := hHc.comp productToST.continuous
  have hpull : B =ᵐ[volume] fun p => chartJCutoffHST ν τ e w (productToST p) :=
    (B0448.measurePreserving_ofLp.symm).quasiMeasurePreserving.ae_eq_comp hHraw.symm
  have hS : MeasurableSet chartCentral := measurableSet_Ioo.prod MeasurableSet.univ
  have hBcentral : B =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν τ p)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hS]
    filter_upwards [hpull] with p hp hpS
    have ht : |p.1| ≤ 1 / 8 := by
      rw [abs_le]
      constructor <;> linarith [hpS.1.1, hpS.1.2]
    have hχ := resolventTimeCutoff_eq_one ht
    simpa [B, chartJCutoffHST, productToST, hχ] using hp
  have hchosen := chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e τ
  have hEqOn := Measure.eqOn_open_of_ae_eq (hchosen.trans hBcentral.symm)
    isOpen_chartCentral (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e τ).continuousOn
    hBcont.continuousOn
  have hp : (0, (Real.sqrt ν)⁻¹ • y) ∈ chartCentral := by
    simp [chartCentral]
  have hpoint := hEqOn hp
  have hsourceBound :
      ‖Hc (productToST (0, (Real.sqrt ν)⁻¹ • y))‖ ≤ K := by
    have hreal : (eLpNorm (chartJCutoffFST ν τ e w b a)
        (ENNReal.ofReal qR) volume).toReal ≤ C.toReal :=
      ENNReal.toReal_mono hCtop.ne (hCuniform τ)
    have hker : 0 ≤ (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal := by positivity
    calc
      _ ≤ (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal *
          (eLpNorm (chartJCutoffFST ν τ e w b a) (ENNReal.ofReal qR) volume).toReal :=
        hHbound (productToST (0, (Real.sqrt ν)⁻¹ • y))
      _ ≤ K := by
        dsimp [K]
        exact mul_le_mul_of_nonneg_left hreal hker
  have hcomplex :
      ‖globalChartRep hP1 hqq' hq hν hTime hLap e τ y‖ ≤ K := by
    change ‖f (0, (Real.sqrt ν)⁻¹ • y)‖ ≤ K
    change ‖chosenLocalChart hP1 hqq' hq hν hTime hLap e τ
      (0, (Real.sqrt ν)⁻¹ • y)‖ ≤ K
    rw [hpoint]
    change ‖Hc (productToST (0, (Real.sqrt ν)⁻¹ • y))‖ ≤ K
    exact hsourceBound
  exact hcomplex

end UnforcedLeray.B0449
