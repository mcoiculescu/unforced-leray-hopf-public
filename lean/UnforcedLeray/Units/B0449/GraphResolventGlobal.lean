import UnforcedLeray.Units.B0449.GraphResolventGlue

/-!
# Gluing the B0449 local continuous chart representatives

The local resolvent argument gives a continuous representative on the central part of every
comoving chart. This file selects those candidates and uses exact chart transitions to produce a
globally continuous scalar representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
variable (e : CVec3)

/-- A selected continuous candidate in the chart centered at `τ`. -/
noncomputable def chosenLocalChart (τ : ℝ) : ℝ × Space → ℂ :=
  Classical.choose (chartJ_cutoff_local_continuous_rep hP1 hqq' hq hν hTime hLap τ e)

theorem continuous_chosenLocalChart (τ : ℝ) :
    Continuous (chosenLocalChart hP1 hqq' hq hν hTime hLap e τ) :=
  (Classical.choose_spec
    (chartJ_cutoff_local_continuous_rep hP1 hqq' hq hν hTime hLap τ e)).1

theorem chosenLocalChart_ae (τ : ℝ) :
    chosenLocalChart hP1 hqq' hq hν hTime hLap e τ =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν τ p)) :=
  (Classical.choose_spec
    (chartJ_cutoff_local_continuous_rep hP1 hqq' hq hν hTime hLap τ e)).2

/-- The scalar chart representative at a physical point, using the chart centered at its phase. -/
noncomputable def globalChartRep (τ : ℝ) (y : Space) : ℂ :=
  chosenLocalChart hP1 hqq' hq hν hTime hLap e τ
    (0, (Real.sqrt ν)⁻¹ • y)

/-- The local expression in one fixed chart. -/
noncomputable def fixedChartExpression (τ₀ : ℝ) (p : ℝ × Space) : ℂ :=
  chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀
    (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • ((Real.sqrt ν)⁻¹ • p.2))

theorem continuous_fixedChartExpression (τ₀ : ℝ) :
    Continuous (fixedChartExpression hP1 hqq' hq hν hTime hLap e τ₀) := by
  unfold fixedChartExpression
  exact (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀).comp (by fun_prop)

theorem globalChartRep_eq_fixedChartExpression {τ₀ τ : ℝ} {y : Space}
    (ht : |τ - τ₀| < 1 / 8) :
    globalChartRep hP1 hqq' hq hν hTime hLap e τ y =
      fixedChartExpression hP1 hqq' hq hν hTime hLap e τ₀ (τ, y) := by
  let d := τ - τ₀
  let z := (Real.sqrt ν)⁻¹ • y
  let p : ℝ × Space := (d, Real.exp (d / 2) • z)
  have hcancel : Real.exp (-d / 2) * Real.exp (d / 2) = 1 := by
    rw [← Real.exp_add]
    have harg : -d / 2 + d / 2 = 0 := by ring
    rw [harg, Real.exp_zero]
  have htrans : chartTransition d p = (0, z) := by
    apply Prod.ext
    · change d + -d = 0
      ring
    · simp [p, chartTransition, smul_smul, hcancel]
  have hp : p ∈ chartOverlap d := by
    change p ∈ chartCentral ∧ chartTransition d p ∈ chartCentral
    simp only [chartCentral, Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rw [abs_lt] at ht
      constructor <;> linarith
    · rw [htrans]
      norm_num
  have hEq := local_chart_candidates_eqOn_overlap hν w τ₀ d e
    (chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀)
    (chosenLocalChart hP1 hqq' hq hν hTime hLap e (τ₀ + d))
    (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀)
    (continuous_chosenLocalChart hP1 hqq' hq hν hTime hLap e (τ₀ + d))
    (chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e τ₀)
    (chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e (τ₀ + d))
  have hpoint := hEq hp
  change chosenLocalChart hP1 hqq' hq hν hTime hLap e τ
      (0, (Real.sqrt ν)⁻¹ • y) =
    chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀
      (τ - τ₀, Real.exp ((τ - τ₀) / 2) • ((Real.sqrt ν)⁻¹ • y))
  simpa [d, z, p, htrans] using hpoint.symm

theorem continuous_globalChartRep : Continuous
    (fun p : ℝ × Space => globalChartRep hP1 hqq' hq hν hTime hLap e p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let τ₀ := p.1
  have hpatch : ContinuousAt
      (fixedChartExpression hP1 hqq' hq hν hTime hLap e τ₀) p :=
    (continuous_fixedChartExpression hP1 hqq' hq hν hTime hLap e τ₀).continuousAt
  have hnear : ∀ᶠ x : ℝ × Space in 𝓝 p, |x.1 - τ₀| < 1 / 8 := by
    have hopen : IsOpen {x : ℝ × Space | x.1 ∈ Ioo (τ₀ - 1 / 8) (τ₀ + 1 / 8)} :=
      isOpen_Ioo.preimage continuous_fst
    have hmem : p ∈ {x : ℝ × Space | x.1 ∈ Ioo (τ₀ - 1 / 8) (τ₀ + 1 / 8)} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor <;> simp [τ₀]
    filter_upwards [hopen.mem_nhds hmem] with x hx
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have heq : (fun x : ℝ × Space =>
      globalChartRep hP1 hqq' hq hν hTime hLap e x.1 x.2) =ᶠ[𝓝 p]
      fixedChartExpression hP1 hqq' hq hν hTime hLap e τ₀ := by
    filter_upwards [hnear] with x hx
    exact globalChartRep_eq_fixedChartExpression hP1 hqq' hq hν hTime hLap e
      (τ₀ := τ₀) (τ := x.1) (y := x.2) (by simpa [τ₀] using hx)
  exact hpatch.congr heq.symm

end UnforcedLeray.B0449
