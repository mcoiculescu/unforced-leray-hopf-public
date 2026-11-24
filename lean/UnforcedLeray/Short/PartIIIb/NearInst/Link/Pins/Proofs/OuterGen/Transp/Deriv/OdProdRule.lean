import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odProdRule : OD_ProdRule := by
  unfold OD_ProdRule
  intro E _ _ s M A x a' x' hA hcont ha hx
  rw [hasDerivWithinAt_iff_isLittleO] at ha hx ⊢
  have hM' : 0 < |M| + 1 := by positivity
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hc3 : 0 < c / 3 := by positivity
  have hc4 : 0 < c / (3 * (|M| + 1)) := by positivity
  have e1 := ha.bound hc3
  have e2 := hx.bound hc4
  have e3 : ∀ᶠ r in 𝓝[s] (0 : ℝ), ‖A r x' - A 0 x'‖ < c / 3 := by
    have ht : Tendsto (fun r => A r x') (𝓝[s] 0) (𝓝 (A 0 x')) := hcont x'
    exact (tendsto_iff_norm_sub_tendsto_zero.1 ht).eventually (Iio_mem_nhds hc3)
  have hAM : ∀ᶠ r in 𝓝[s] (0 : ℝ), ‖A r‖ ≤ |M| + 1 :=
    eventually_nhdsWithin_of_forall fun r hr => (hA r hr).trans (by linarith [le_abs_self M])
  filter_upwards [e1, e2, e3, hAM] with r h1 h2 h3 h4
  have b1 : ‖A r (x 0) - A 0 (x 0) - (r - 0) • a'‖ ≤ c / 3 * ‖r - 0‖ := h1
  have b2' : ‖x r - x 0 - (r - 0) • x'‖ ≤ c / (3 * (|M| + 1)) * ‖r - 0‖ := h2
  have key : A r (x r) - A 0 (x 0) - (r - 0) • (a' + A 0 x') =
      (A r (x 0) - A 0 (x 0) - (r - 0) • a') + A r (x r - x 0 - (r - 0) • x') +
        (r - 0) • (A r x' - A 0 x') := by
    simp only [map_sub, ContinuousLinearMap.map_smul_of_tower, smul_sub, smul_add]
    abel
  show ‖A r (x r) - A 0 (x 0) - (r - 0) • (a' + A 0 x')‖ ≤ c * ‖r - 0‖
  rw [key]
  have b2 : ‖A r (x r - x 0 - (r - 0) • x')‖ ≤ c / 3 * ‖r - 0‖ := by
    calc ‖A r (x r - x 0 - (r - 0) • x')‖
        ≤ ‖A r‖ * ‖x r - x 0 - (r - 0) • x'‖ := (A r).le_opNorm _
      _ ≤ (|M| + 1) * (c / (3 * (|M| + 1)) * ‖r - 0‖) :=
          mul_le_mul h4 b2' (norm_nonneg _) hM'.le
      _ = c / 3 * ‖r - 0‖ := by field_simp
  have b3 : ‖(r - 0) • (A r x' - A 0 x')‖ ≤ ‖r - 0‖ * (c / 3) := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left h3.le (norm_nonneg _)
  calc ‖(A r (x 0) - A 0 (x 0) - (r - 0) • a') + A r (x r - x 0 - (r - 0) • x') +
        (r - 0) • (A r x' - A 0 x')‖
      ≤ ‖(A r (x 0) - A 0 (x 0) - (r - 0) • a') + A r (x r - x 0 - (r - 0) • x')‖ +
          ‖(r - 0) • (A r x' - A 0 x')‖ := norm_add_le _ _
    _ ≤ ‖A r (x 0) - A 0 (x 0) - (r - 0) • a'‖ + ‖A r (x r - x 0 - (r - 0) • x')‖ +
          ‖(r - 0) • (A r x' - A 0 x')‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ c * ‖r - 0‖ := by nlinarith [b1, b2, b3, norm_nonneg (r - 0)]

end UnforcedLeray.Short.PartIIIb.NearInst
