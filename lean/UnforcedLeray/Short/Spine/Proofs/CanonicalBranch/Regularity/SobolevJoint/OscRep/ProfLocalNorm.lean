import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!
# Leaf A3 of `Spine:SP-CAN/4/4/1`: the local `L²` bound (`OscProfLocalNorm`)

Proves `UnforcedLeray.Short.Spine.OscProfLocalNorm`, declared in
`Short/Spine/Sub/SP_CAN4_4_1.lean` (not edited here). Source of record:
`the November 2 reference manuscript`, line 1086 and lines 1134-1140.

Argument: `‖prof q‖² = ∫_{(0,∞)} ‖profFun q r‖² w(r) dr` with `w(r) = G(r)⁻¹ r = 4π e^{r²/4} r`
(`B0094.inner_prof`, `B0094.weight_eq`). The integrand is nonnegative and integrable on `(0,∞)`
(`B0010.memLp_iff_integrableOn` applied to `B0094.memLp_profFun`). Since `0 < a`, the interval
`(a, b]` lies in `(0, ∞)`, so the integral over `(a, b]` is at most the integral over `(0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

/-- Pointwise identity: the integrand of the pairing `⟪prof q, prof q⟫` is the real function
`‖profFun q r‖² w(r)`, cast to `ℂ`. -/
theorem profLocalNorm_integrand (q : ℂ[X]) (r : ℝ) :
    UnforcedLeray.B0094.profFun q r *
        (starRingEnd ℂ) (UnforcedLeray.B0094.profFun q r) *
          (((UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) =
      ((‖UnforcedLeray.B0094.profFun q r‖ ^ 2 *
          ((UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r) : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- `‖prof q‖²` is the weighted integral of `‖profFun q‖²` over `(0, ∞)`. -/
theorem profLocalNorm_norm_sq (q : ℂ[X]) :
    ‖UnforcedLeray.B0094.prof q‖ ^ 2 =
      ∫ r in Ioi 0, ‖UnforcedLeray.B0094.profFun q r‖ ^ 2 *
        ((UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r) := by
  have h1 : ⟪UnforcedLeray.B0094.prof q, UnforcedLeray.B0094.prof q⟫_ℂ =
      ((∫ r in Ioi 0, ‖UnforcedLeray.B0094.profFun q r‖ ^ 2 *
        ((UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r) : ℝ) : ℂ) := by
    rw [UnforcedLeray.B0094.inner_prof,
      setIntegral_congr_fun measurableSet_Ioi (fun r _ => profLocalNorm_integrand q r)]
    exact integral_ofReal
  have h2 : ⟪UnforcedLeray.B0094.prof q, UnforcedLeray.B0094.prof q⟫_ℂ =
      ((‖UnforcedLeray.B0094.prof q‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  exact Complex.ofReal_injective (h2.symm.trans h1)

/-- **Leaf A3** (`OscProfLocalNorm`): for `0 < a ≤ b`, the weighted `L²` mass
`∫_a^b |profFun q|² · 4π e^{r²/4} r dr` is at most `‖prof q‖²` in `X_G`. -/
theorem oscProfLocalNorm_proof : UnforcedLeray.Short.Spine.OscProfLocalNorm := by
  unfold OscProfLocalNorm
  intro q a b ha hab
  have hint : IntegrableOn (fun r : ℝ => ‖UnforcedLeray.B0094.profFun q r‖ ^ 2 *
      ((UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r)) (Ioi 0) :=
    (UnforcedLeray.B0010.memLp_iff_integrableOn
      (UnforcedLeray.B0094.continuous_profFun q).aestronglyMeasurable).1
      (UnforcedLeray.B0094.memLp_profFun q)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun r : ℝ =>
      ‖UnforcedLeray.B0094.profFun q r‖ ^ 2 *
        ((UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (inv_nonneg.2 (UnforcedLeray.B0010.radialGaussianWeight_pos r).le)
        (Set.mem_Ioi.1 hr).le)
  have hle : volume.restrict (Ioc a b) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)) le_rfl
  have hw : ∀ r : ℝ, oscWeight r = (UnforcedLeray.B0010.radialGaussianWeight r)⁻¹ * r :=
    fun r => (UnforcedLeray.B0094.weight_eq r).symm
  simp only [hw]
  rw [profLocalNorm_norm_sq q, intervalIntegral.integral_of_le hab]
  exact integral_mono_measure hle hnn hint

end UnforcedLeray.Short.Spine
