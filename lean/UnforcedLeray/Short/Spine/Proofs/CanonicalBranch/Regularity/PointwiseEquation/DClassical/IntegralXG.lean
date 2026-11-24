import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3

/-!
# Leaf 6 of `Spine:SP-CAN/4/5/3`: the `xGMeasure` integral as a weighted Lebesgue integral

Proves `UnforcedLeray.Short.Spine.IntegralXGEq`. Source of record:
`the November 2 reference manuscript` line 1086 and lines 1134-1140.

Proof: `xGMeasure` is `(volume.restrict (Ioi 0)).withDensity xGDensity`, so
`integral_withDensity_eq_integral_smul` turns the integral into `∫_{(0,∞)} xGDensity r • F r`.
On `(0, ∞)` the density is the real number `wDens r = 4π e^{r²/4} r`, whose complex copy is `wC r`.
Since `F r = 0` for `r ≤ 0` (because `r < a`), the integral over `(0, ∞)` equals the integral over `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

/-- **Leaf 6, proof.** The `xGMeasure` integral of `F` equals the weighted Lebesgue integral
`∫ wC r * F r`, for `F` vanishing on `(-∞, a)` and `(b, ∞)` with `0 < a`. -/
theorem integralXGEq_proof : IntegralXGEq := by
  intro F a b ha hFa _
  -- Step 1: the xGMeasure integral is the integral over (0, ∞) against the density.
  have h1 : ∫ r, F r ∂xGMeasure = ∫ r in Ioi (0 : ℝ), (xGDensity r) • F r := by
    rw [xGMeasure]
    exact integral_withDensity_eq_integral_smul measurable_xGDensity F
  -- Step 2: on (0, ∞) the density coincides with wC.
  have h2 : ∫ r in Ioi (0 : ℝ), (xGDensity r) • F r = ∫ r in Ioi (0 : ℝ), wC r * F r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    show (xGDensity r) • F r = wC r * F r
    have hr' : (0 : ℝ) < r := hr
    have hnn : (0 : ℝ) ≤ 4 * Real.pi * Real.exp (r ^ 2 / 4) * r := (wDens_pos hr').le
    have hc : ((xGDensity r : NNReal) : ℝ) = wDens r := by
      rw [xGDensity_eq]
      exact Real.coe_toNNReal _ hnn
    rw [NNReal.smul_def, Complex.real_smul, hc]
    rfl
  -- Step 3: the integral over (0, ∞) is the integral over ℝ, since F vanishes for r ≤ 0.
  have h3 : ∫ r in Ioi (0 : ℝ), wC r * F r = ∫ r, wC r * F r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hr' : r ≤ 0 := by simpa [Set.mem_Ioi] using hr
    have hra : r < a := lt_of_le_of_lt hr' ha
    rw [hFa r hra, mul_zero]
  exact h1.trans (h2.trans h3)

end UnforcedLeray.Short.Spine
