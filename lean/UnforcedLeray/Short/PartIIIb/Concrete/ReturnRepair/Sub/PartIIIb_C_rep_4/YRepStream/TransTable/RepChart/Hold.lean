import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart.Chart2

/-!
# `RepChart/Hold`: Hölder `1/2 = 4/11 + 3/22` in `z` at each phase (source 5338-5339)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RC

theorem ltauLq_two_le {P : ℝ} (M f : ℝ → Space → ℝ≥0∞)
    (hM : Measurable (Function.uncurry M)) (hf : Measurable (Function.uncurry f)) (ρ : ℝ≥0∞)
    (hMb : ∀ τ, (∫⁻ y, M τ y ^ (11 / 4 : ℝ)) ^ (4 / 11 : ℝ) ≤ ρ) :
    IIIa.ltauLq P 2 (fun τ y => M τ y * f τ y) ≤ ρ * IIIa.ltauLq P (22 / 3) f := by
  have hpq : (11 / 8 : ℝ).HolderConjugate (11 / 3) := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hpt : ∀ τ, (∫⁻ y, (M τ y * f τ y) ^ (2 : ℝ)) ≤
      ρ ^ (2 : ℝ) * (∫⁻ y, f τ y ^ (22 / 3 : ℝ)) ^ (3 / 11 : ℝ) := by
    intro τ
    have hMs : Measurable (M τ) := hM.comp (measurable_const.prodMk measurable_id)
    have hfs : Measurable (f τ) := hf.comp (measurable_const.prodMk measurable_id)
    have h1 : ∫⁻ y, (M τ y * f τ y) ^ (2 : ℝ) =
        ∫⁻ y, ((fun y => M τ y ^ (2 : ℝ)) * (fun y => f τ y ^ (2 : ℝ))) y := by
      refine lintegral_congr fun y => ?_
      simp only [Pi.mul_apply]
      exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    rw [h1]
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq (hMs.pow_const _).aemeasurable
      (hfs.pow_const _).aemeasurable).trans ?_
    have e1 : ∀ y, (M τ y ^ (2 : ℝ)) ^ (11 / 8 : ℝ) = M τ y ^ (11 / 4 : ℝ) := fun y => by
      rw [← ENNReal.rpow_mul]; norm_num
    have e2 : ∀ y, (f τ y ^ (2 : ℝ)) ^ (11 / 3 : ℝ) = f τ y ^ (22 / 3 : ℝ) := fun y => by
      rw [← ENNReal.rpow_mul]; norm_num
    simp_rw [e1, e2]
    refine mul_le_mul' ?_ (by norm_num)
    have : (∫⁻ y, M τ y ^ (11 / 4 : ℝ)) ^ (1 / (11 / 8 : ℝ)) =
        ((∫⁻ y, M τ y ^ (11 / 4 : ℝ)) ^ (4 / 11 : ℝ)) ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_mul]; norm_num
    rw [this]
    exact ENNReal.rpow_le_rpow (hMb τ) (by norm_num)
  unfold IIIa.ltauLq
  have hnorm : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [hnorm, ENNReal.rpow_one]
  have h2 : (2 : ℝ) / (22 / 3) = 3 / 11 := by norm_num
  rw [h2]
  calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, (M τ y * f τ y) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ρ ^ (2 : ℝ) *
          (∫⁻ y, f τ y ^ (22 / 3 : ℝ)) ^ (3 / 11 : ℝ)) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono fun τ => hpt τ))
          (by norm_num)
    _ = ρ * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
          (∫⁻ y, f τ y ^ (22 / 3 : ℝ)) ^ (3 / 11 : ℝ)) ^ (1 / 2 : ℝ) := by
        have hm : Measurable fun τ : ℝ => (∫⁻ y, f τ y ^ (22 / 3 : ℝ)) ^ (3 / 11 : ℝ) := by
          have h1 : Measurable (fun p : ℝ × Space => f p.1 p.2 ^ (22 / 3 : ℝ)) := hf.pow_const _
          exact (h1.lintegral_prod_right' (ν := (volume : Measure Space))).pow_const _
        rw [lintegral_const_mul _ hm, show (ENNReal.ofReal P)⁻¹ * (ρ ^ (2 : ℝ) *
            ∫⁻ τ in Ioc 0 P, (∫⁻ y, f τ y ^ (22 / 3 : ℝ)) ^ (3 / 11 : ℝ)) =
          ρ ^ (2 : ℝ) * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
            (∫⁻ y, f τ y ^ (22 / 3 : ℝ)) ^ (3 / 11 : ℝ)) by ring,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num

end RC

end UnforcedLeray.Short.PartIIIb.Concrete

end
