import UnforcedLeray.Units.B0449.GraphResolventPhaseTrace

/-!
# A real continuous representative of a B0449 graph field

Three scalar coordinate projections of the glued chart field assemble into a continuous real
vector representative of the actual graph element. The every-phase trace identity supplies the
slice identification; the phase-trace AE theorem then gives the required product AE equality.
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

local notation "qE" => ENNReal.ofReal qR

/-- The complex coordinate vector used to read one component through `dotL`. -/
def complexCoordinate (i : Fin 3) : CVec3 :=
  WithLp.toLp 2 (Pi.single i (1 : ℂ))

theorem dotL_complexCoordinate (i : Fin 3) (v : CVec3) :
    dotL (complexCoordinate i) v = v i := by
  rw [dotL_apply]
  simp [complexCoordinate]

/-- Assemble the three scalar chart projections into a real spatial vector field. -/
def globalRealChartRep (τ : ℝ) (y : Space) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    (globalChartRep hP1 hqq' hq hν hTime hLap (complexCoordinate i) τ y).re)

theorem continuous_globalRealChartRep : Continuous
    (fun p : ℝ × Space => globalRealChartRep hP1 hqq' hq hν hTime hLap p.1 p.2) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun i => by
      exact (Complex.continuous_re.comp
        (continuous_globalChartRep hP1 hqq' hq hν hTime hLap (complexCoordinate i))).comp
          continuous_id)

/-- Coordinatewise real part of a complex three-vector. -/
def realPartVector (v : CVec3) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 => (v i).re)

theorem globalRealChartRep_ae_phaseRepC (τ : ℝ) :
    (fun y => globalRealChartRep hP1 hqq' hq hν hTime hLap τ y) =ᵐ[volume]
      (fun y => realPartVector (phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top)
        hTime (τ : AddCircle P) y)) := by
  have hcoord : ∀ i : Fin 3,
      (fun y => (globalChartRep hP1 hqq' hq hν hTime hLap
        (complexCoordinate i) τ y).re) =ᵐ[volume]
        (fun y => (phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top)
          hTime (τ : AddCircle P) y i).re) := by
    intro i
    have hglobal := globalChartRep_ae_phaseScalar hP1 hqq' hq hν hTime hLap
      (complexCoordinate i) τ
    have hcoerce := coeFn_phaseScalarPath hTime (complexCoordinate i) τ
    filter_upwards [hglobal, hcoerce] with y hy hy'
    rw [dotL_complexCoordinate] at hy'
    exact congrArg Complex.re (hy.trans hy')
  rw [Filter.EventuallyEq]
  filter_upwards [ae_all_iff.2 hcoord] with y hy
  ext i
  exact hy i

end UnforcedLeray.B0449
