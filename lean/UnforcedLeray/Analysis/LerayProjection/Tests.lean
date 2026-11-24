import UnforcedLeray.Analysis.SobolevGraph.Pairing
import UnforcedLeray.TestFunctions

/-!
# Genuine compact-test gradients in L²(R³; R³)

The L² gradient of a compact smooth scalar test is the finite sum of its
coordinate derivatives against the Euclidean coordinate vectors. Its Hilbert
pairing with an arbitrary L² vector field is the actual integrable weak
divergence test pairing. This provides the concrete tests for the Leray
solenoidal subspace; no differential constraint on the vector field is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Leray

/-- The actual L² class of the gradient of a compact smooth spatial test. -/
def testGradient (φ : Space → ℝ) (hφ : IsSpatialTest φ) : L2Space :=
  ∑ i : Fin 3, SobolevGraph.testVector (spatialTestDerivative i φ)
    (hφ.derivative i) (coordinateVector i)

/-- The representative of the L² class is almost everywhere the coordinate gradient. -/
theorem coeFn_testGradient (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    (testGradient φ hφ : SpatialField) =ᵐ[volume]
      fun x => ∑ i : Fin 3, spatialTestDerivative i φ x • coordinateVector i := by
  have htests : ∀ᵐ x ∂volume, ∀ i : Fin 3,
      SobolevGraph.testVector (spatialTestDerivative i φ) (hφ.derivative i)
        (coordinateVector i) x = spatialTestDerivative i φ x • coordinateVector i :=
    ae_all_iff.mpr fun i => SobolevGraph.coeFn_testVector
      (spatialTestDerivative i φ) (hφ.derivative i) (coordinateVector i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin 3 => SobolevGraph.testVector (spatialTestDerivative i φ)
      (hφ.derivative i) (coordinateVector i)), htests] with x hx htests_x
  exact hx.trans (Finset.sum_congr rfl fun i _ => htests_x i)

/-- Euclidean coordinates identify the gradient pairing with its usual scalar sum. -/
theorem gradient_inner (φ : Space → ℝ) (x v : Space) :
    inner ℝ (∑ i : Fin 3, spatialTestDerivative i φ x • coordinateVector i) v =
      ∑ i : Fin 3, v i * spatialTestDerivative i φ x := by
  simp [sum_inner, real_inner_smul_left, coordinateVector,
    EuclideanSpace.inner_single_left, mul_comm]

/-- L² Hölder integrability of the full weak divergence test pairing. -/
theorem gradient_pairing_integrable (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) :
    Integrable (fun x => ∑ i : Fin 3, (F x) i * spatialTestDerivative i φ x) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (testGradient φ hφ) F).congr ?_
  filter_upwards [coeFn_testGradient φ hφ] with x hx
  rw [hx, gradient_inner]

/-- The Hilbert pairing is exactly the integrable weak divergence test integral. -/
theorem testGradient_inner (φ : Space → ℝ) (hφ : IsSpatialTest φ) (F : L2Space) :
    inner ℝ (testGradient φ hφ) F =
      ∫ x : Space, ∑ i : Fin 3, (F x) i * spatialTestDerivative i φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_testGradient φ hφ] with x hx
  rw [hx, gradient_inner]

end UnforcedLeray.Leray
