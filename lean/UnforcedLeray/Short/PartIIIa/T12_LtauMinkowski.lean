import UnforcedLeray.Short.PartIIIa.Targets
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# T12: Minkowski's integral inequality for the phase norms (SP 3670-3674)

Proves `UnforcedLeray.Short.IIIa.LtauMinkowski` (statement in `Targets.lean`): for `P > 0` and a
tensor source `T` with jointly measurable entries,
`‖T‖_{L²_τ L¹_z} ≤ ∫ ‖T(·, z)‖_{L²_τ} dz`, where `L²_τ` is the normalised phase norm on
`(0, P]`, `ltauLq P 1 (srcNorm T)` is the left side and `∫⁻ z, ltauAt P (srcNorm T · z)` the right.

Proof. The left side is `(P⁻¹ ∫_{(0,P]} (∫_z |T(τ,z)|)² dτ)^{1/2}`, and the right side is
`∫_z (P⁻¹ ∫_{(0,P]} |T(τ,z)|² dτ)^{1/2} dz`. Pull the constant `P⁻¹` out (`ENNReal.mul_rpow_of_nonneg`
and `lintegral_const_mul'`) and apply Minkowski's integral inequality
`NonUniqueEuler.Conv.lintegral_lintegral_rpow_le` with `μ = volume.restrict (Ioc 0 P)`,
`ν = volume` on `Space` and `p = 2`, to the jointly measurable `F(τ, z) = |T(τ, z)|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **T12** (`LtauMinkowski`, SP 3670-3674): Minkowski's integral inequality
`‖T‖_{L²_τL¹_z} ≤ ∫ ‖T(·,z)‖_{L²_τ} dz` for the normalised phase norms on `(0, P]`. -/
theorem ltauMinkowski : UnforcedLeray.Short.IIIa.LtauMinkowski := by
  intro P hP T hT
  -- Joint measurability of `(τ, z) ↦ |T(τ, z)|`.
  have hTn : Measurable fun p : ℝ × Space => tensorNorm (T p.1 p.2) := by
    unfold tensorNorm
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (hT i j).pow_const 2
  have hFm : Measurable (Function.uncurry fun τ z => srcNorm T τ z) :=
    ENNReal.measurable_ofReal.comp hTn
  -- Minkowski's integral inequality, with the `L²` norm in `τ` and the `L¹` norm in `z`.
  have hmink : (∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ z : Space, srcNorm T τ z) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      ∫⁻ z : Space, (∫⁻ τ in Ioc (0 : ℝ) P, srcNorm T τ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact NonUniqueEuler.Conv.lintegral_lintegral_rpow_le
      (μ := volume.restrict (Ioc (0 : ℝ) P)) (ν := (volume : Measure Space))
      (F := fun τ z => srcNorm T τ z) hFm.aemeasurable (p := (2 : ℝ)) (by norm_num)
  have hc : (ENNReal.ofReal P)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hP).ne'
  unfold ltauLq ltauAt
  simp only [ENNReal.rpow_one, div_one]
  calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ z : Space, srcNorm T τ z) ^ (2 : ℝ)) ^
        (1 / (2 : ℝ))
      = (ENNReal.ofReal P)⁻¹ ^ (1 / (2 : ℝ)) *
          (∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ z : Space, srcNorm T τ z) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / (2 : ℝ))
    _ ≤ (ENNReal.ofReal P)⁻¹ ^ (1 / (2 : ℝ)) *
          ∫⁻ z : Space, (∫⁻ τ in Ioc (0 : ℝ) P, srcNorm T τ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = ∫⁻ z : Space, (ENNReal.ofReal P)⁻¹ ^ (1 / (2 : ℝ)) *
          (∫⁻ τ in Ioc (0 : ℝ) P, srcNorm T τ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        (lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / (2 : ℝ)) hc)).symm
    _ = ∫⁻ z : Space, ((ENNReal.ofReal P)⁻¹ *
          ∫⁻ τ in Ioc (0 : ℝ) P, srcNorm T τ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        lintegral_congr fun z =>
          (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / (2 : ℝ))).symm

end UnforcedLeray.Short.IIIa
