import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiMajRep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.KerSrcMeasurable
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/12`: Minkowski's integral inequality over the source atoms

Source `the November 2 reference manuscript` 5590 ("Minkowski"), with the
representation `psiMaj ≤ ∫ phKer · srcW` of `PsiMajRep.lean`.  For every output set `X`,
`‖psiMaj‖_{L²(X)} ≤ ∫ srcW(a) ‖phKer(·; a)‖_{L²(X)} da`.

Route: pointwise `psiMaj ≤ ∫ phKer · srcW` and monotonicity of `rpow`; then Minkowski's
integral inequality (`UnforcedLeray.PlanarBS.Conv.lintegral_lintegral_rpow_le`, outputs in
`volume.restrict X`, atoms in `volume`, exponent `2`); then for each atom
`(∫_X (phKer·W)²)^{1/2} = W (∫_X phKer²)^{1/2}` by `ENNReal.mul_rpow_of_nonneg` and
`lintegral_mul_const`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- Measurability of the kernel in the output variable, for a fixed atom. -/
theorem phKer_measurable_output (θ σ : ℝ) (z : Space) :
    Measurable (fun x : ℝ × Space => phKer θ x.1 x.2 σ z) := by
  unfold phKer
  have hc : MeasurableSet {x : ℝ × Space | σ < x.1 ∧ ϱ z < θ * ϱ x.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_const.mul (measurable_ϱ.comp measurable_snd)))
  have m1 : Measurable (fun x : ℝ × Space => ENNReal.ofReal (Real.exp ((σ - x.1) / 2) / 2)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have m2 : Measurable (fun x : ℝ × Space =>
      ENNReal.ofReal ((‖x.2 - Real.exp ((σ - x.1) / 2) • z‖ ^ 4)⁻¹)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  exact Measurable.ite hc (m1.mul m2) measurable_const

theorem psiAtomsMinkowski : PsiAtomsMinkowski := by
  intro R c θ G hG X
  have hW : ∀ W : ℝ≥0∞, (W ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = W := fun W => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have key : ∀ a : ℝ × Space,
      (∫⁻ x in X, (phKer θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
        srcW R c G a.1 a.2 * (∫⁻ x in X, phKer θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro a
    have h1 : ∀ x : ℝ × Space, (phKer θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ) =
        phKer θ x.1 x.2 a.1 a.2 ^ (2 : ℝ) * srcW R c G a.1 a.2 ^ (2 : ℝ) :=
      fun x => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    simp only [h1]
    rw [lintegral_mul_const _ ((phKer_measurable_output θ a.1 a.2).pow_const (2 : ℝ)),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hW, mul_comm]
  have hM := UnforcedLeray.PlanarBS.Conv.lintegral_lintegral_rpow_le
    (μ := volume.restrict X) (ν := (volume : Measure (ℝ × Space)))
    (F := fun x a => phKer θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2)
    (kerSrcMeasurable R c θ G hG).aemeasurable (p := 2) (by norm_num)
  calc (∫⁻ x in X, psiMaj R c θ G x.1 x.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ x in X, (∫⁻ a : ℝ × Space, phKer θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow
          (lintegral_mono fun x => ENNReal.rpow_le_rpow (psiMajRep R c θ G hG x.1 x.2) (by norm_num))
          (by norm_num)
    _ ≤ ∫⁻ a : ℝ × Space, (∫⁻ x in X, (phKer θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ) := hM
    _ = ∫⁻ a : ℝ × Space, srcW R c G a.1 a.2 *
          (∫⁻ x in X, phKer θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        lintegral_congr key

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
