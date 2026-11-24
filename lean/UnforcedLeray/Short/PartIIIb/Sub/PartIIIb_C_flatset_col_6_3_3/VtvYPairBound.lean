import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.BandVanish

/-!
# Pairing bound for `Y` on a box (source 3511-3514, 4464-4467)

`⟨ω(s),φ⟩ = ∫ b₀∂_ηφ - b₁∂_qφ` (third clause of `IsBiotSavart`); for `φ` vanishing for `|η| > R`
the integrand lives on the box `cell ∩ {|η| ≤ R}`, where `b(s,·)` is `L¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvYPairBound : VtvYPairBound := by
  intro ν c μ tr ω g b G f H R s hs φ hφ hz K hK
  have hBS := H.2.2.2.2.1 s hs
  have hb : ∀ i : Fin 2, IntegrableOn (fun x => b (s, x) i) (vtvBox c R) := fun i =>
    integrableOn_vtvBox_of_memLp R (hBS.1 i)
  have h0 := pd_vanish hz 0
  have h1 := pd_vanish hz 1
  set F : ℝ × ℝ → ℂ := fun x =>
    b (s, x) 0 * (B0579.pd 1 φ x : ℂ) - b (s, x) 1 * (B0579.pd 0 φ x : ℂ) with hF
  have hint : ∫ x in B0579.cell c, ω s x * (φ x : ℂ) = ∫ x in vtvBox c R, F x := by
    rw [hBS.2.2 φ hφ]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B0579.measurableSet_cell c)
      (vtvBox_subset_cell c R) fun x hx => ?_
    have hx2 : R < |x.2| := by
      by_contra hcon
      exact hx.2 ⟨hx.1, not_lt.1 hcon⟩
    simp [hF, h0 x hx2, h1 x hx2]
  have hG : IntegrableOn (fun x => K * (‖b (s, x) 0‖ + ‖b (s, x) 1‖)) (vtvBox c R) :=
    (((hb 0).norm).add (hb 1).norm).const_mul K
  have hle : ‖∫ x in vtvBox c R, F x‖ ≤ K * vtvDB c R b s := by
    unfold vtvDB
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le hG (Eventually.of_forall fun x => ?_)
    have e0 := hK x 0
    have e1 := hK x 1
    have hK0 : 0 ≤ K := (abs_nonneg _).trans e0
    calc ‖F x‖ ≤ ‖b (s, x) 0 * (B0579.pd 1 φ x : ℂ)‖ + ‖b (s, x) 1 * (B0579.pd 0 φ x : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖b (s, x) 0‖ * |B0579.pd 1 φ x| + ‖b (s, x) 1‖ * |B0579.pd 0 φ x| := by
          simp [norm_mul]
      _ ≤ ‖b (s, x) 0‖ * K + ‖b (s, x) 1‖ * K := by
          gcongr
      _ = K * (‖b (s, x) 0‖ + ‖b (s, x) 1‖) := by ring
  unfold vtvY
  rw [norm_mul, hint]
  calc ‖(s : ℂ) ^ (μ : ℂ)‖ * ‖∫ x in vtvBox c R, F x‖
      ≤ ‖(s : ℂ) ^ (μ : ℂ)‖ * (K * vtvDB c R b s) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
