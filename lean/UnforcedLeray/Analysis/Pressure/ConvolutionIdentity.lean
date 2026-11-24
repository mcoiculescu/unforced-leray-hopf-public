import UnforcedLeray.Analysis.Pressure.ConvolutionPairing
import UnforcedLeray.Analysis.Pressure.Spatial
import UnforcedLeray.Analysis.Pressure.HeatTest
import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import UnforcedLeray.Analysis.LerayProjection.TranslationTests

/-!
# The actual Newtonian convolution tested against compact functions

The Newtonian-gradient kernel is split into the already proved near and far
Lᵖ classes. Hölder against the compact test gives absolute integrability on
R³ × R³, so the passage between the literal convolution and the translated
kernel pairing is a genuine Fubini theorem.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace UnforcedLeray.PressureAnalysis

private theorem holder_newton_near : ENNReal.HolderTriple (15 / 14) 15 1 := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff, ENNReal.toReal_div]

private theorem holder_newton_far : ENNReal.HolderTriple (5 / 3) (5 / 2) 1 := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff, ENNReal.toReal_div]

/-- Every translate of the whole Newton kernel has an integrable test pairing. -/
theorem newtonKernel_mul_test_integrable (i : Fin 3) {ψ : Space → ℝ}
    (hψ : IsSpatialTest ψ) (y : Space) :
    Integrable (fun x => newtonGradientKernel i (x - y) * ψ x) volume := by
  have hn : Integrable (fun x => nearNewtonKernel 1 i (x - y) * ψ x) volume := by
    let := holder_newton_near
    exact kernel_test_product_integrable (nearNewtonKernel_memLp (by norm_num) i)
      (hψ.memLp 15) y
  have hf : Integrable (fun x => farNewtonKernel 1 i (x - y) * ψ x) volume := by
    let := holder_newton_far
    exact kernel_test_product_integrable (farNewtonKernel_memLp (by norm_num) i)
      (hψ.memLp (5 / 2)) y
  have he : (fun x => newtonGradientKernel i (x - y) * ψ x) =
      (fun x => nearNewtonKernel 1 i (x - y) * ψ x + farNewtonKernel 1 i (x - y) * ψ x) := by
    funext x
    rw [← add_mul, nearNewtonKernel_add_far]
  rw [he]
  exact hn.add hf

/-- The actual Newton-forcing-test product is integrable on the full product space. -/
theorem newton_convolution_test_integrable (i : Fin 3) {f ψ : Space → ℝ}
    (hf : Integrable f volume) (hψ : IsSpatialTest ψ) :
    Integrable (fun z : Space × Space =>
      newtonGradientKernel i (z.1 - z.2) * f z.2 * ψ z.1)
      ((volume : Measure Space).prod volume) := by
  have hn : Integrable (fun z : Space × Space =>
      nearNewtonKernel 1 i (z.1 - z.2) * f z.2 * ψ z.1)
      ((volume : Measure Space).prod volume) := by
    let := holder_newton_near
    exact convolution_test_integrable (nearNewtonKernel_memLp (by norm_num) i)
      (hψ.memLp 15) hf
  have hfar : Integrable (fun z : Space × Space =>
      farNewtonKernel 1 i (z.1 - z.2) * f z.2 * ψ z.1)
      ((volume : Measure Space).prod volume) := by
    let := holder_newton_far
    exact convolution_test_integrable (farNewtonKernel_memLp (by norm_num) i)
      (hψ.memLp (5 / 2)) hf
  apply (hn.add hfar).congr
  exact Eventually.of_forall fun z => by
    simp only [Pi.add_apply]
    rw [← add_mul, ← add_mul, nearNewtonKernel_add_far]

/-- Compact testing of the actual convolution gives an integrable scalar function. -/
theorem newtonComponent_mul_test_integrable (i : Fin 3) {f ψ : Space → ℝ}
    (hf : Integrable f volume) (hψ : IsSpatialTest ψ) :
    Integrable (fun x => newtonComponent i f x * ψ x) volume := by
  simpa only [newtonComponent, integral_mul_const] using
    (newton_convolution_test_integrable i hf hψ).integral_prod_left

/-- Fubini for the whole Newtonian-gradient kernel, justified by the actual split estimates. -/
theorem integral_newtonComponent_mul_test (i : Fin 3) {f ψ : Space → ℝ}
    (hf : Integrable f volume) (hψ : IsSpatialTest ψ) :
    (∫ x, newtonComponent i f x * ψ x) =
      ∫ y, f y * (∫ x, newtonGradientKernel i (x - y) * ψ x) := by
  calc
    _ = ∫ x, ∫ y, newtonGradientKernel i (x - y) * f y * ψ x := by
      simp only [newtonComponent, integral_mul_const]
    _ = ∫ y, ∫ x, newtonGradientKernel i (x - y) * f y * ψ x :=
      integral_integral_swap (newton_convolution_test_integrable i hf hψ)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring

/-- The concrete coordinate Laplacian commutes with translation of the test. -/
theorem scalar_laplacian_translate (a : Space) (φ : Space → ℝ) (x : Space) :
    Heat.laplacian (fun y => φ (y + a)) x = Heat.laplacian φ (x + a) := by
  change (∑ i : Fin 3, spatialTestDerivative i
    (spatialTestDerivative i (fun y => φ (y + a))) x) =
      ∑ i : Fin 3, spatialTestDerivative i (spatialTestDerivative i φ) (x + a)
  apply Finset.sum_congr rfl
  intro i _
  have he : spatialTestDerivative i (fun y => φ (y + a)) =
      fun y => spatialTestDerivative i φ (y + a) := by
    funext y
    exact Leray.spatialTestDerivative_translate a i φ y
  rw [he, Leray.spatialTestDerivative_translate]

/-- Lebesgue translation moves the translated kernel onto the compact test. -/
theorem newtonKernel_laplacian_pairing_translate (i : Fin 3) (φ : Space → ℝ) (y : Space) :
    (∫ x, newtonGradientKernel i (x - y) * Heat.laplacian φ x) =
      ∫ x, newtonGradientKernel i x * Heat.laplacian (fun z => φ (z + y)) x := by
  calc
    _ = ∫ x, newtonGradientKernel i ((x + y) - y) * Heat.laplacian φ (x + y) :=
      (integral_add_right_eq_self
        (fun x => newtonGradientKernel i (x - y) * Heat.laplacian φ x) y).symm
    _ = _ := by simp only [add_sub_cancel_right, scalar_laplacian_translate]

/-- The actual left-hand side of the pressure Poisson test identity is integrable. -/
theorem newtonComponent_laplacian_test_integrable (i : Fin 3) {f φ : Space → ℝ}
    (hf1 : MemLp f 1 volume) (hφ : IsSpatialTest φ) :
    Integrable (fun x => newtonComponent i f x * Heat.laplacian φ x) volume :=
  newtonComponent_mul_test_integrable i (memLp_one_iff_integrable.mp hf1) (scalarTest_laplacian hφ)

/-- The actual forcing paired with a compact test derivative is integrable. -/
theorem forcing_partial_test_integrable (i : Fin 3) {f φ : Space → ℝ}
    (hf1 : MemLp f 1 volume) (hφ : IsSpatialTest φ) :
    Integrable (fun y => f y * spatialTestDerivative i φ y) volume := by
  exact memLp_one_iff_integrable.mp ((hφ.derivative_memLp i ⊤).mul' hf1)

/-- The proved normalized kernel identity holds at every translated test centre. -/
theorem newtonKernel_laplacian_test_translated (i : Fin 3) {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (y : Space) :
    (∫ x, newtonGradientKernel i (x - y) * Heat.laplacian φ x) =
      spatialTestDerivative i φ y := by
  rw [newtonKernel_laplacian_pairing_translate]
  have h := newtonGradientKernel_laplacian_test i (Leray.isSpatialTest_translate y hφ)
  simpa only [Leray.spatialTestDerivative_translate, zero_add] using h

/-- The literal real Newtonian convolution solves the pressure Poisson equation
against every compact smooth test. Both sides are actual integrable pairings;
the normalization and the kernel distribution identity are proved dependencies. -/
theorem newtonComponent_laplacian_test (i : Fin 3) {f φ : Space → ℝ}
    (hf1 : MemLp f 1 volume) (hφ : IsSpatialTest φ) :
    (∫ x, newtonComponent i f x * Heat.laplacian φ x) =
      ∫ y, f y * spatialTestDerivative i φ y := by
  rw [integral_newtonComponent_mul_test i (memLp_one_iff_integrable.mp hf1)
    (scalarTest_laplacian hφ)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [newtonKernel_laplacian_test_translated i hφ y]

end UnforcedLeray.PressureAnalysis
