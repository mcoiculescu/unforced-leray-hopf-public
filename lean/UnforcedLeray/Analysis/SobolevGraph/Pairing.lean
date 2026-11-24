import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Continuous L² test pairings on genuine Euclidean three-space

Compact smooth scalar tests, multiplied by constant vectors in R³, give
continuous real linear functionals on the vector-valued L² space. The
functionals are identified with the actual vector-valued Lebesgue integrals;
Hölder integrability is proved before using those integrals.

This uses Mathlib's concrete L² Hilbert space and no formal PDE assumption.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.SobolevGraph

private theorem scalarTest_memLp (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    MemLp φ 2 volume :=
  hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact

private theorem vectorTest_memLp (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) :
    MemLp (fun x => φ x • v) 2 volume :=
  (hφ.smooth.continuous.smul continuous_const).memLp_of_hasCompactSupport
    (hφ.compact.smul_right (f' := fun _ => v))

/-- The actual L² equivalence class of the compact vector test `φ(x)v`. -/
def testVector (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) : L2Space :=
  (vectorTest_memLp φ hφ v).toLp (fun x => φ x • v)

theorem coeFn_testVector (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) :
    (testVector φ hφ v : SpatialField) =ᵐ[volume] fun x => φ x • v :=
  (vectorTest_memLp φ hφ v).coeFn_toLp

/-- Hölder's inequality gives an honest integrable vector-valued test product. -/
theorem pairing_integrable (φ : Space → ℝ) (hφ : IsSpatialTest φ) (F : L2Space) :
    Integrable (fun x => φ x • F x) volume := by
  have hm : MemLp (φ • (F : SpatialField)) 1 volume :=
    (Lp.memLp F).smul (scalarTest_memLp φ hφ)
  exact memLp_one_iff_integrable.mp hm

/-- The continuous real linear test-pairing functional on vector-valued L². -/
def pairing (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) : L2Space →L[ℝ] ℝ :=
  innerSL ℝ (testVector φ hφ v)

/-- The abstract Hilbert pairing is exactly the expected vector Lebesgue integral. -/
theorem pairing_apply (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) (F : L2Space) :
    pairing φ hφ v F = inner ℝ v (∫ x : Space, φ x • F x) := by
  change inner ℝ (testVector φ hφ v) F = _
  rw [L2.inner_def, ← integral_inner (pairing_integrable φ hφ F) v]
  apply integral_congr_ae
  filter_upwards [coeFn_testVector φ hφ v] with x hx
  simp only [hx, real_inner_smul_left, real_inner_smul_right]

end UnforcedLeray.SobolevGraph
