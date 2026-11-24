import UnforcedLeray.Statement
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Concrete spatial test-function calculus

The derivative closure argument follows the general test-function construction
in NonUniqueEuler/Defs/Infra/Sobolev.lean, commit
d81c3f456505f8a3e8211f2a9f63313d0599ed5a (Apache-2.0, attribution in
THIRD_PARTY_NOTICES.md). Here the domain is actual Euclidean R³ and the scalar
field is real, matching the weak derivatives in Statement.lean.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace UnforcedLeray
namespace IsSpatialTest

variable {φ : Space → ℝ}

theorem continuous (hφ : IsSpatialTest φ) : Continuous φ := hφ.smooth.continuous

/-- Every coordinate derivative is again a compact smooth spatial test. -/
theorem derivative (hφ : IsSpatialTest φ) (i : Fin 3) :
    IsSpatialTest (spatialTestDerivative i φ) := by
  constructor
  · exact (ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).clm_apply contDiff_const
  · exact hφ.compact.fderiv_apply ℝ (coordinateVector i)

/-- Taking a coordinate derivative does not enlarge the closed support. -/
theorem derivative_support_subset (_hφ : IsSpatialTest φ) (i : Fin 3) :
    tsupport (spatialTestDerivative i φ) ⊆ tsupport φ := by
  exact tsupport_fderiv_apply_subset ℝ (coordinateVector i)

/-- All Lp requirements on compact smooth scalar tests are actual theorems. -/
theorem memLp (hφ : IsSpatialTest φ) (p : ℝ≥0∞) : MemLp φ p volume :=
  hφ.continuous.memLp_of_hasCompactSupport hφ.compact

theorem derivative_memLp (hφ : IsSpatialTest φ) (i : Fin 3) (p : ℝ≥0∞) :
    MemLp (spatialTestDerivative i φ) p volume := (hφ.derivative i).memLp p

theorem integrable (hφ : IsSpatialTest φ) : Integrable φ :=
  hφ.continuous.integrable_of_hasCompactSupport hφ.compact

theorem derivative_integrable (hφ : IsSpatialTest φ) (i : Fin 3) :
    Integrable (spatialTestDerivative i φ) := (hφ.derivative i).integrable

end IsSpatialTest
end UnforcedLeray
