import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, toolkit leaf `EbFluxBound`: `ebFluxBound`

Source of record: `the November 2 reference manuscript`, lines 276-282.
Target: `EbFluxBound` (`Short/PartI/Sub/T02_3_10.lean`, line 177). The three hypotheses
`EbStripBound`, `EbDerivBounds`, `EbSliceSmooth` are the toolkit statements of the same file, used
here only as hypotheses.

## Argument

Fix `R ≥ 1` and `s ∈ [0, T]`, and write `w = v s`. Put

* `g₁ z = ⟨w z, ∂_η w z⟩`, with `|g₁| ≤ Mv Kv`,
* `g₂ z = ‖w z‖² w₁ z`, with `|g₂| ≤ Mv² Mv`,
* `g₃ z = p s z · w₁ z`, with `|g₃| ≤ |Mp| Mv`.

All three are continuous, since `EbSliceSmooth` makes the slices `C^∞` and `∂_η` of a `C¹` function is
continuous. Then `T_visc = -2ν D - 2ν ∫ φ' g₁`, `T_conv = ∫ φ' g₂` and `T_pres = 2 ∫ φ' g₃`, where
`D = ebDissipation ≥ 0`. `EbStripBound` bounds each `∫ φ' g_i` by `K₀ c B_i`. Hence the sum of the three
right sides is at most `2ν K₀ c Mv Kv + K₀ c Mv² Mv + 2 K₀ c |Mp| Mv`, a constant independent of `R`
and `s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **Leaf `EbFluxBound`**: from the strip estimate, the derivative bounds and slice smoothness, the
three right sides of the viscous, convective and pressure identities are bounded uniformly in `R`
and `s`. -/
theorem ebFluxBound : EbStripBound → EbDerivBounds → EbSliceSmooth → EbFluxBound := by
  intro hS hD hSm
  obtain ⟨K0, hK0, hstrip⟩ := hS
  intro ν c T Mp v p hν hc hcl hb hp
  obtain ⟨Mv, Kv, hMv, hKv, hbd⟩ := hD ν c T v p hcl hb
  have hK1 : 0 ≤ K0 * c := mul_nonneg hK0 hc.le
  have hMK : 0 ≤ Mv * Kv := mul_nonneg hMv hKv
  have hMp : 0 ≤ |Mp| := abs_nonneg Mp
  have h2ν : 0 ≤ 2 * ν := by linarith
  refine ⟨2 * ν * (K0 * c * (Mv * Kv)) + K0 * c * (Mv ^ 2 * Mv)
      + 2 * (K0 * c * (|Mp| * Mv)), ?_, ?_⟩
  · have e1 : 0 ≤ 2 * ν * (K0 * c * (Mv * Kv)) := mul_nonneg h2ν (mul_nonneg hK1 hMK)
    have e2 : 0 ≤ K0 * c * (Mv ^ 2 * Mv) :=
      mul_nonneg hK1 (mul_nonneg (pow_nonneg hMv 2) hMv)
    have e3 : 0 ≤ 2 * (K0 * c * (|Mp| * Mv)) :=
      mul_nonneg (by norm_num) (mul_nonneg hK1 (mul_nonneg hMp hMv))
    exact add_nonneg (add_nonneg e1 e2) e3
  intro R hR s hs
  -- smoothness of the slice, and continuity of its `η`-derivative
  have hvs : ContDiff ℝ ∞ (v s) := (hSm ν c T v p hcl s hs).1
  have hvc : Continuous (v s) := hvs.continuous
  have hpc : Continuous (p s) := (hSm ν c T v p hcl s hs).2.continuous
  have hv1 : ContDiff ℝ 1 (v s) := hvs.of_le (by norm_num)
  have hpe : Continuous (Cyl.partialEta (v s)) := (Cyl.C1_partial_of_contDiff hv1).2
  have hcoord : Continuous (fun z : Plane => v s z 1) :=
    (PiLp.continuous_apply 2 _ 1).comp hvc
  -- pointwise bounds
  have hcoordb : ∀ z : Plane, |v s z 1| ≤ Mv := fun z => by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (v s z) 1).trans (hbd s hs z).1
  have hg1c : Continuous (fun z : Plane => inner ℝ (v s z) (Cyl.partialEta (v s) z)) :=
    hvc.inner hpe
  have hg2c : Continuous (fun z : Plane => ‖v s z‖ ^ 2 * v s z 1) :=
    (hvc.norm.pow 2).mul hcoord
  have hg3c : Continuous (fun z : Plane => p s z * v s z 1) :=
    hpc.mul hcoord
  have hg1b : ∀ z : Plane, |inner ℝ (v s z) (Cyl.partialEta (v s) z)| ≤ Mv * Kv := fun z =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hbd s hs z).1 (hbd s hs z).2 (norm_nonneg _) hMv)
  have hg2b : ∀ z : Plane, |‖v s z‖ ^ 2 * v s z 1| ≤ Mv ^ 2 * Mv := fun z => by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbd s hs z).1 2) (hcoordb z)
      (abs_nonneg _) (sq_nonneg Mv)
  have hg3b : ∀ z : Plane, |p s z * v s z 1| ≤ |Mp| * Mv := fun z => by
    rw [abs_mul]
    exact mul_le_mul ((hp s hs z).trans (le_abs_self Mp)) (hcoordb z) (abs_nonneg _) hMp
  -- the strip estimate for each of the three integrands
  have hI1 : |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
      inner ℝ (v s z) (Cyl.partialEta (v s) z)| ≤ K0 * c * (Mv * Kv) :=
    hstrip c R hc hR (fun z : Plane => inner ℝ (v s z) (Cyl.partialEta (v s) z)) (Mv * Kv)
      hg1c hg1b
  have hI2 : |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (‖v s z‖ ^ 2 * v s z 1)| ≤
      K0 * c * (Mv ^ 2 * Mv) :=
    hstrip c R hc hR (fun z : Plane => ‖v s z‖ ^ 2 * v s z 1) (Mv ^ 2 * Mv) hg2c hg2b
  have hI3 : |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (p s z * v s z 1)| ≤
      K0 * c * (|Mp| * Mv) :=
    hstrip c R hc hR (fun z : Plane => p s z * v s z 1) (|Mp| * Mv) hg3c hg3b
  -- rearranging the integrands of `ebConvRhs` and `ebPresRhs` to the form `φ' · g`
  have eI2 : ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2 =
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (‖v s z‖ ^ 2 * v s z 1) :=
    integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eI3 : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1 =
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (p s z * v s z 1) :=
    integral_congr_ae (ae_of_all _ fun z => mul_assoc _ _ _)
  -- the dissipation is nonnegative
  have hD0 : 0 ≤ ebDissipation c v R s := by
    unfold ebDissipation
    exact integral_nonneg fun z => mul_nonneg (etaCutoff_nonneg R z.2) (gradNormSq_nonneg _ z)
  have hνD : 0 ≤ 2 * ν * ebDissipation c v R s := mul_nonneg h2ν hD0
  obtain ⟨hI1lo, -⟩ := abs_le.mp hI1
  have hνI1 : 2 * ν * (-(K0 * c * (Mv * Kv))) ≤
      2 * ν * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
        inner ℝ (v s z) (Cyl.partialEta (v s) z) :=
    mul_le_mul_of_nonneg_left hI1lo h2ν
  have hI2up : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (‖v s z‖ ^ 2 * v s z 1) ≤
      K0 * c * (Mv ^ 2 * Mv) := (abs_le.mp hI2).2
  have hI3up : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (p s z * v s z 1) ≤
      K0 * c * (|Mp| * Mv) := (abs_le.mp hI3).2
  unfold ebViscousRhs ebConvRhs ebPresRhs
  linarith

end UnforcedLeray.Short.PartI
