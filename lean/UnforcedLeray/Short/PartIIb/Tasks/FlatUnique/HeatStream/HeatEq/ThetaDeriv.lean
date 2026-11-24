import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Smooth
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeMajorant
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative

/-!
# Part II-b, helper for leaf `PartII-b:T11/3/4` (`HeatConvEq`): the heat age derivative

Source of record: `the November 2 reference manuscript`, line 1924 (`e^{ν τ Δ}`).

For a nice stream `ζ` and `θ₀ > 0`, the map `θ ↦ ∫ G_θ(w) ζ(z - w) dw` has derivative
`∫ (∂_θ G)_{θ₀}(w) ζ(z - w) dw` at `θ₀`. Domination on `θ ∈ (θ₀/2, 2θ₀)` comes from the local
majorant `abs_heatKernel2AgeDerivative_le_local` and the boundedness of `ζ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Differentiation in the heat age `θ` of the convolution `∫ G_θ(w) ζ(z - w) dw` at `θ₀ > 0`. -/
theorem hce_theta_hasDerivAt {c : ℝ} (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (z : ℝ × ℝ) :
    HasDerivAt (fun θ : ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w))
      (∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w * ζ (z - w)) θ₀ := by
  obtain ⟨B, hB0, hB⟩ := hcs_nice_iteratedFDeriv_bound hc hζ 0
  have hζB : ∀ y : ℝ × ℝ, ‖ζ y‖ ≤ B := fun y => by simpa using hB y
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hζm : ∀ w : ℝ × ℝ, AEStronglyMeasurable (fun w : ℝ × ℝ => ζ (z - w)) (volume : Measure (ℝ × ℝ)) :=
    fun w => ((hζc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hsmem : Ioo (θ₀ / 2) (2 * θ₀) ∈ 𝓝 θ₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hk0 : ∀ θ : ℝ, 0 < θ → ∀ w : ℝ × ℝ, 0 ≤ UnforcedLeray.B0284.heatKernel2 θ w :=
    fun θ hθ w => UnforcedLeray.B0284.heatKernel2_nonneg hθ w
  have hF_meas : ∀ᶠ θ in 𝓝 θ₀,
      AEStronglyMeasurable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w))
        (volume : Measure (ℝ × ℝ)) := by
    filter_upwards [hsmem] with θ hθ
    exact (UnforcedLeray.B0284.integrable_heatKernel2 (by linarith [hθ.1] : 0 < θ)).aestronglyMeasurable.mul
      (hζm 0)
  have hF_int : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ₀ w * ζ (z - w)) :=
    (UnforcedLeray.B0284.integrable_heatKernel2 hθ₀).mul_bdd (hζm 0)
      (ae_of_all _ fun w => hζB (z - w))
  have hF'_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
      UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w * ζ (z - w))
      (volume : Measure (ℝ × ℝ)) :=
    (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀).aestronglyMeasurable.mul
      (hζm 0)
  set C : ℝ := 4 * (θ₀⁻¹ ^ 2 + 2 / θ₀) * B with hCdef
  have hbound_int : Integrable (fun w : ℝ × ℝ =>
      C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w)) :=
    (UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2
      (by linarith : (0 : ℝ) < 2 * θ₀)).const_mul C
  have h_bound : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ s ∈ Ioo (θ₀ / 2) (2 * θ₀),
      ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * ζ (z - w)‖ ≤
        C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w) := by
    refine ae_of_all _ fun w s hs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hage := UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local hθ₀ hs.1 hs.2 w
    have hpos : 0 ≤ (1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w :=
      mul_nonneg (by positivity) (hk0 (2 * θ₀) (by linarith) w)
    have hz : |ζ (z - w)| ≤ B := by simpa [Real.norm_eq_abs] using hζB (z - w)
    calc |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w| * |ζ (z - w)|
        ≤ (4 * (θ₀⁻¹ ^ 2 + 2 / θ₀) * ((1 + w.1 ^ 2 + w.2 ^ 2) *
            UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w)) * B :=
          mul_le_mul hage hz (abs_nonneg _) (mul_nonneg (by positivity) hpos)
      _ = C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w) := by
          rw [hCdef]
          ring
  have h_diff : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ s ∈ Ioo (θ₀ / 2) (2 * θ₀),
      HasDerivAt (fun θ : ℝ => UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w))
        (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * ζ (z - w)) s := by
    refine ae_of_all _ fun w s hs => ?_
    have hs0 : 0 < s := lt_trans (by linarith) hs.1
    exact (UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age hs0 w).mul_const (ζ (z - w))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (ℝ × ℝ))) (x₀ := θ₀)
    (s := Ioo (θ₀ / 2) (2 * θ₀))
    (F := fun θ w => UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w))
    (F' := fun θ w => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ζ (z - w))
    (bound := fun w => C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w))
    hsmem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact key.2

end UnforcedLeray.Short.IIb
