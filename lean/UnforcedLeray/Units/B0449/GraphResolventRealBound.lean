import UnforcedLeray.Units.B0449.GraphResolventUniformBound

/-!
# A uniform spatial bound for the real graph representative
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

/-- A phase-independent pointwise bound for the real three-vector representative. -/
theorem exists_globalRealChartRep_uniform_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ y,
      ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y‖ ≤ M := by
  let B : Fin 3 → ℝ := fun i => Classical.choose
    (exists_globalChartRep_uniform_bound hP1 hqq' hq hν hTime hLap (complexCoordinate i))
  have hBnonneg : ∀ i, 0 ≤ B i := by
    intro i
    exact (Classical.choose_spec
      (exists_globalChartRep_uniform_bound hP1 hqq' hq hν hTime hLap (complexCoordinate i))).1
  have hBbound : ∀ i τ y,
      ‖globalChartRep hP1 hqq' hq hν hTime hLap (complexCoordinate i) τ y‖ ≤ B i := by
    intro i τ y
    exact (Classical.choose_spec
      (exists_globalChartRep_uniform_bound hP1 hqq' hq hν hTime hLap (complexCoordinate i))).2 τ y
  let M : ℝ := ∑ i : Fin 3, B i
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun i _ => hBnonneg i
  refine ⟨3 * M, by positivity, ?_⟩
  intro τ y
  have hcoord : ∀ i : Fin 3,
      |(globalChartRep hP1 hqq' hq hν hTime hLap (complexCoordinate i) τ y).re| ≤ M := by
    intro i
    have hproj := hBbound i τ y
    have hsum : B i ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum (fun j _ => hBnonneg j) (Finset.mem_univ i)
    exact (Complex.abs_re_le_norm _).trans (hproj.trans hsum)
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin 3,
      ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y i‖ ^ 2) ≤
      ∑ _i : Fin 3, M ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y i‖ ≤ M := by
      simpa [globalRealChartRep, PiLp.toLp_apply, Real.norm_eq_abs] using hcoord i
    have hprod : 0 ≤ (M - ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y i‖) *
        (M + ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y i‖) :=
      mul_nonneg (sub_nonneg.mpr hi') (by positivity)
    nlinarith
  have hroot : Real.sqrt (3 * M ^ 2) ≤ 3 * M := by
    have hsqrt : Real.sqrt (3 * M ^ 2) = Real.sqrt 3 * M := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
    rw [hsqrt]
    have hsqrt3 : Real.sqrt 3 ≤ 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul_of_nonneg_right hsqrt3 hM
  calc
    _ ≤ Real.sqrt (3 * M ^ 2) := Real.sqrt_le_sqrt (by simpa using hsum)
    _ ≤ 3 * M := hroot

end UnforcedLeray.B0449
