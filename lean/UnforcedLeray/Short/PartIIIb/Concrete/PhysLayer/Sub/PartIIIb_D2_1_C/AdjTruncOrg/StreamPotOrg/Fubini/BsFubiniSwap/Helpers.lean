import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsPairIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helpers for the Biot-Savart Fubini swap (`BSFubiniSwap`)

Source `the November 2 reference manuscript` lines 1351-1362.
Basis-direction dot products, a componentwise integrability criterion for `CVec3`-valued
functions, the scalar triple product identity, integrability of `y ↦ K(y-z) × A(y)`, and
a family of continuous compactly supported bumps `φ_n = 1` on `‖y‖ ≤ n+1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- A scalar multiple of a basis vector pairs with `v` to the corresponding coordinate. -/
theorem bsDotL_smul_single (c : ℂ) (i : Fin 3) (v : CVec3) :
    dotL (c • (EuclideanSpace.single i (1 : ℂ))) v = c * v i := by
  fin_cases i <;> simp [dotL_apply, Fin.sum_univ_three, EuclideanSpace.single_apply]

/-- The norm of a `CVec3` is bounded by the sum of the moduli of its coordinates. -/
theorem bsNorm_le_sum (v : CVec3) : ‖v‖ ≤ ∑ i : Fin 3, ‖v i‖ := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three]
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1), norm_nonneg (v 2),
    mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 1)),
    mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 2)),
    mul_nonneg (norm_nonneg (v 1)) (norm_nonneg (v 2))]

/-- A `CVec3`-valued function is integrable once each coordinate is integrable. -/
theorem bsIntegrable_of_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → CVec3}
    (hg : AEStronglyMeasurable g μ) (hi : ∀ i : Fin 3, Integrable (fun a => g a i) μ) :
    Integrable g μ := by
  refine Integrable.mono' (integrable_finset_sum Finset.univ (fun i _ => (hi i).norm)) hg ?_
  exact Filter.Eventually.of_forall (fun a => bsNorm_le_sum (g a))

/-- Scalar triple product: `a · (f × K) = f · (K × a)`. -/
theorem bsTriple (a f K : CVec3) : dotL a (crossC f K) = dotL f (crossC K a) := by
  simp [dotL_apply, Fin.sum_univ_three, crossC] <;> ring

/-- Strong measurability of `y ↦ K(y-z) × A(y)`. -/
theorem bsKernelCross_aesm (A : Space → CVec3) (hA : Continuous A) (z : Space) :
    AEStronglyMeasurable (fun y : Space => crossC (bsKernel (y - z)) (A y)) volume := by
  have hsub : Measurable (fun y : Space => y - z) := measurable_id.sub_const z
  have hKa : AEStronglyMeasurable (fun y : Space => bsKernel (y - z)) volume :=
    (bsKernel_measurable.comp hsub).aestronglyMeasurable
  exact crossC_continuous'.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => crossC a b)
    hKa hA.aestronglyMeasurable

/-- For fixed `z`, `y ↦ K(y-z) × A(y)` is integrable for continuous compactly supported `A`. -/
theorem bsKernelCross_integrable (A : Space → CVec3) (hA : Continuous A)
    (hAint : ∀ z : Space, Integrable (fun y : Space => ‖A y‖ * ‖bsKernel (y - z)‖) volume)
    (z : Space) :
    Integrable (fun y : Space => crossC (bsKernel (y - z)) (A y)) volume := by
  refine Integrable.mono' ((hAint z).const_mul 4) (bsKernelCross_aesm A hA z) ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  show ‖crossC (bsKernel (y - z)) (A y)‖ ≤ 4 * (‖A y‖ * ‖bsKernel (y - z)‖)
  have h := crossC_norm_le' (bsKernel (y - z)) (A y)
  calc ‖crossC (bsKernel (y - z)) (A y)‖ ≤ 4 * ‖bsKernel (y - z)‖ * ‖A y‖ := h
    _ = 4 * (‖A y‖ * ‖bsKernel (y - z)‖) := by ring

/-- Bump of radius `n+1` (equal to `1` on `‖y‖ ≤ n+1`, support in the ball of radius `n+2`). -/
def bsBumpN (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem bsBumpN_one (n : ℕ) {y : Space} (h : ‖y‖ ≤ (n : ℝ) + 1) : bsBumpN n y = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  exact h

/-- The basis-direction bump `y ↦ φ_n(y) e_i`. -/
def bsBasisBump (n : ℕ) (i : Fin 3) : Space → CVec3 :=
  fun y => ((bsBumpN n y : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ)

theorem bsBasisBump_continuous (n : ℕ) (i : Fin 3) : Continuous (bsBasisBump n i) :=
  (Complex.continuous_ofReal.comp (bsBumpN n).continuous).smul continuous_const

theorem bsBasisBump_hasCompactSupport (n : ℕ) (i : Fin 3) :
    HasCompactSupport (bsBasisBump n i) :=
  (bsBumpN n).hasCompactSupport.comp_left
    (g := fun r : ℝ => ((r : ℂ)) • EuclideanSpace.single i (1 : ℂ)) (by simp)

end UnforcedLeray.Short.PartIIIb.Concrete
