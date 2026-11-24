import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Assembly

/-!
# `PartII-a:N01/9/1/3/1`: `energyFieldSub`

Source `the November 2 reference manuscript` lines 3426-3430: the difference of two
energy fields is an energy field.  `energyLoc` and `zeroEntrance` come from the pointwise bound
`|x - y|² ≤ 2|x|² + 2|y|²` (`vnorm2`, `tnorm2`), with the smaller of the two `δ`s; `divFreeAE` and
`weakGradAE` for a.e. age are linear in the data, the slices being integrable there because the
`weakGradAE` integrability clauses of each field give them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

private theorem efs_norm_sub_sq_le (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  nlinarith [mul_self_le_mul_self h0 h1, sq_nonneg (‖a‖ - ‖b‖)]

private theorem efs_vnorm2_sub_le (a b : Fin 2 → ℂ) :
    vnorm2 (fun i => a i - b i) ^ 2 ≤ 2 * vnorm2 a ^ 2 + 2 * vnorm2 b ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
  · simp only [Fin.sum_univ_two]
    linarith [efs_norm_sub_sq_le (a 0) (b 0), efs_norm_sub_sq_le (a 1) (b 1)]
  all_goals exact Finset.sum_nonneg fun i _ => sq_nonneg _

private theorem efs_tnorm2_sub_le (A B : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => A i j - B i j) ^ 2 ≤ 2 * tnorm2 A ^ 2 + 2 * tnorm2 B ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
  · simp only [Fin.sum_univ_two]
    linarith [efs_norm_sub_sq_le (A 0 0) (B 0 0), efs_norm_sub_sq_le (A 0 1) (B 0 1),
      efs_norm_sub_sq_le (A 1 0) (B 1 0), efs_norm_sub_sq_le (A 1 1) (B 1 1)]
  all_goals exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

private theorem efs_continuous_vnorm2 : Continuous vnorm2 := by
  unfold vnorm2
  refine Real.continuous_sqrt.comp ?_
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).norm).pow 2

private theorem efs_continuous_tnorm2 : Continuous tnorm2 := by
  unfold tnorm2
  refine Real.continuous_sqrt.comp ?_
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_apply j).comp (continuous_apply i)).norm).pow 2

private theorem efs_measurable_energy {c : ℝ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (h : IsEnergyFieldAE c b G) :
    Measurable fun p => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 := by
  have hb : Measurable b := measurable_pi_lambda _ h.measurable
  have hG : Measurable G :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => h.gradMeasurable i j
  exact ((efs_continuous_vnorm2.measurable.comp hb).pow_const 2).add
    ((efs_continuous_tnorm2.measurable.comp hG).pow_const 2)

private theorem efs_measurable_vnorm2 {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (h : ∀ i, Measurable fun p => b p i) :
    Measurable fun p => vnorm2 (b p) ^ 2 := by
  have hb : Measurable b := measurable_pi_lambda _ h
  exact (efs_continuous_vnorm2.measurable.comp hb).pow_const 2

private theorem efs_ofReal_le (x y z : ℝ) (hx : x ≤ 2 * y + 2 * z) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ENNReal.ofReal x ≤ 2 * ENNReal.ofReal y + 2 * ENNReal.ofReal z := by
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (2 * y + 2 * z) := ENNReal.ofReal_le_ofReal hx
    _ = 2 * ENNReal.ofReal y + 2 * ENNReal.ofReal z := by
      rw [ENNReal.ofReal_add (show (0:ℝ) ≤ 2 * y by linarith) (show (0:ℝ) ≤ 2 * z by linarith),
        ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
        ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]

theorem energyFieldSub : EnergyFieldSub := by
  intro c hc b₁ b₂ G₁ G₂ h₁ h₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (h₁.measurable i).sub (h₂.measurable i)
  · intro i j
    exact (h₁.gradMeasurable i j).sub (h₂.gradMeasurable i j)
  · intro s₁ s₂ hs₁ hs₁₂
    have hA := h₁.energyLoc s₁ s₂ hs₁ hs₁₂
    have hB := h₂.energyLoc s₁ s₂ hs₁ hs₁₂
    have hF1 := (efs_measurable_energy h₁).ennreal_ofReal
    have hF2 := (efs_measurable_energy h₂).ennreal_ofReal
    have key : ∀ p, ENNReal.ofReal (vnorm2 (fun i => b₁ p i - b₂ p i) ^ 2
          + tnorm2 (fun i j => G₁ p i j - G₂ p i j) ^ 2)
        ≤ 2 * ENNReal.ofReal (vnorm2 (b₁ p) ^ 2 + tnorm2 (G₁ p) ^ 2)
          + 2 * ENNReal.ofReal (vnorm2 (b₂ p) ^ 2 + tnorm2 (G₂ p) ^ 2) := by
      intro p
      apply efs_ofReal_le
      · linarith [efs_vnorm2_sub_le (b₁ p) (b₂ p), efs_tnorm2_sub_le (G₁ p) (G₂ p)]
      · positivity
      · positivity
    refine lt_of_le_of_lt (lintegral_mono key) ?_
    rw [lintegral_add_left (hF1.const_mul 2), lintegral_const_mul _ hF1, lintegral_const_mul _ hF2]
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hA, ENNReal.mul_lt_top ENNReal.ofNat_lt_top hB⟩
  · obtain ⟨δ₁, hδ₁, hI₁⟩ := h₁.zeroEntrance
    obtain ⟨δ₂, hδ₂, hI₂⟩ := h₂.zeroEntrance
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    have hF1 := (efs_measurable_vnorm2 h₁.measurable).ennreal_ofReal
    have hF2 := (efs_measurable_vnorm2 h₂.measurable).ennreal_ofReal
    have m1 := lt_of_le_of_lt
      (lintegral_mono' (Measure.restrict_mono
        (Set.prod_mono (Ioo_subset_Ioo_right (min_le_left δ₁ δ₂)) subset_rfl) le_rfl) le_rfl) hI₁
    have m2 := lt_of_le_of_lt
      (lintegral_mono' (Measure.restrict_mono
        (Set.prod_mono (Ioo_subset_Ioo_right (min_le_right δ₁ δ₂)) subset_rfl) le_rfl) le_rfl) hI₂
    have key : ∀ p, ENNReal.ofReal (vnorm2 (fun i => b₁ p i - b₂ p i) ^ 2)
        ≤ 2 * ENNReal.ofReal (vnorm2 (b₁ p) ^ 2) + 2 * ENNReal.ofReal (vnorm2 (b₂ p) ^ 2) := by
      intro p
      apply efs_ofReal_le
      · linarith [efs_vnorm2_sub_le (b₁ p) (b₂ p)]
      · positivity
      · positivity
    refine lt_of_le_of_lt (lintegral_mono key) ?_
    rw [lintegral_add_left (hF1.const_mul 2), lintegral_const_mul _ hF1, lintegral_const_mul _ hF2]
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top m1, ENNReal.mul_lt_top ENNReal.ofNat_lt_top m2⟩
  · filter_upwards [h₁.divFreeAE, h₂.divFreeAE, h₁.weakGradAE, h₂.weakGradAE]
      with s hd1 hd2 hw1 hw2 hs ψ hψ
    have I1a : IntegrableOn (fun x => b₁ (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ))
        (UnforcedLeray.B0579.cell c) := ((hw1 hs 0 0).1 ψ hψ).1
    have I1b : IntegrableOn (fun x => b₁ (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ))
        (UnforcedLeray.B0579.cell c) := ((hw1 hs 1 1).1 ψ hψ).1
    have I2a : IntegrableOn (fun x => b₂ (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ))
        (UnforcedLeray.B0579.cell c) := ((hw2 hs 0 0).1 ψ hψ).1
    have I2b : IntegrableOn (fun x => b₂ (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ))
        (UnforcedLeray.B0579.cell c) := ((hw2 hs 1 1).1 ψ hψ).1
    have hA := hd1 hs ψ hψ
    have hB := hd2 hs ψ hψ
    have e : ∀ x : ℝ × ℝ,
        (b₁ (s, x) 0 - b₂ (s, x) 0) * (UnforcedLeray.B0579.pd 0 ψ x : ℂ)
          + (b₁ (s, x) 1 - b₂ (s, x) 1) * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)
        = (b₁ (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ)
            + b₁ (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ))
          - (b₂ (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ)
            + b₂ (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) :=
      fun x => by ring
    show ∫ x in UnforcedLeray.B0579.cell c,
        ((b₁ (s, x) 0 - b₂ (s, x) 0) * (UnforcedLeray.B0579.pd 0 ψ x : ℂ)
          + (b₁ (s, x) 1 - b₂ (s, x) 1) * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0
    simp only [e]
    rw [integral_sub, hA, hB, sub_zero]
    · exact I1a.add I1b
    · exact I2a.add I2b
  · filter_upwards [h₁.weakGradAE, h₂.weakGradAE] with s hw1 hw2 hs i j
    exact UnforcedLeray.Short.IIIa.hasWeakCellDerivC_sub (hw1 hs i j) (hw2 hs i j)

end UnforcedLeray.Short.PartIIa.N01
