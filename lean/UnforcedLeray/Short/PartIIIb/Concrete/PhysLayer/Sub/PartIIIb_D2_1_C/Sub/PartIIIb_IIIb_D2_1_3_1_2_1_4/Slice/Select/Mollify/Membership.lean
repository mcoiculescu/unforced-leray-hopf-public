import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_1
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# `convYMembership`: Young in `y` for the mollified fields

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`convYMol L Φ` is the `y`-convolution of `Φ` with a continuous compactly supported kernel `L`.
Strategy: replace `Φ` by a strongly measurable representative `G`, bound the slices by the
Minkowski/Young inequality `Sob.eLpNorm_cv_le`, and integrate over a period.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A property holding for a.e. slice `t` and every `y` holds almost everywhere on the product. -/
lemma ae_of_ae_slice {R : ℝ × Space → Prop} (h : ∀ᵐ t : ℝ, ∀ y : Space, R (t, y)) :
    ∀ᵐ x : ℝ × Space, R x := by
  have h0 : volume {t : ℝ | ¬ ∀ y : Space, R (t, y)} = 0 := ae_iff.mp h
  rw [ae_iff]
  have hsub : {x : ℝ × Space | ¬ R x} ⊆
      {t : ℝ | ¬ ∀ y : Space, R (t, y)} ×ˢ (Set.univ : Set Space) := by
    intro x hx
    exact ⟨fun h' => hx (h' x.2), Set.mem_univ _⟩
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, h0, zero_mul]

/-- The phase-normalised `Y_2` norm depends only on the a.e. class. -/
lemma phaseLpNorm_congr_ae {P : ℝ} {f g : ℝ × Space → CVec3} (h : f =ᵐ[volume] g) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 f = UnforcedLeray.Short.IIb.phaseLpNorm P 2 g := by
  have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), f x = g x := h
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ y : Space, f (t, y) = g (t, y) :=
    Measure.ae_ae_of_ae_prod h'
  have h2 : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖f (t, y)‖ₑ ^ (2 : ℝ))
      = ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae ((ae_restrict_of_ae h1).mono fun t ht => ?_)
    exact lintegral_congr_ae (ht.mono fun y hy => by simp only [hy])
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  rw [h2]

lemma aux_rpow_sq {A B C : ℝ≥0∞} (h : A ^ (1 / (2 : ℝ)) ≤ C * B ^ (1 / (2 : ℝ))) :
    A ≤ C ^ (2 : ℝ) * B := by
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  have e1 : (1 / (2 : ℝ)) * 2 = 1 := by norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, e1, ENNReal.rpow_one, ENNReal.rpow_one] at h2
  exact h2

lemma aux_outer {p I C : ℝ≥0∞} :
    (p * (C ^ (2 : ℝ) * I)) ^ (1 / (2 : ℝ)) = C * (p * I) ^ (1 / (2 : ℝ)) := by
  rw [mul_left_comm p, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul]
  norm_num

/-- Core Young/Minkowski bound for a strongly measurable representative. -/
lemma core_bound {P : ℝ} (L : Space → ℝ) (hL : Continuous L) (hLi : Integrable L volume)
    (G : ℝ × Space → CVec3) (hG : StronglyMeasurable G) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (convYMol L G)
      ≤ ENNReal.ofReal (∫ y : Space, |L y|) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 G := by
  set C : ℝ≥0∞ := ∫⁻ s : Space, ‖L s‖ₑ with hCdef
  have hCeq : C = ENNReal.ofReal (∫ y : Space, |L y|) := by
    rw [hCdef, ← ofReal_integral_norm_eq_lintegral_enorm hLi]
    simp only [Real.norm_eq_abs]
  have hCtop : C ≠ ⊤ := by
    rw [hCeq]
    exact ENNReal.ofReal_ne_top
  have hC2 : C ^ (2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCtop
  have h2z : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hpt : ∀ t : ℝ, (∫⁻ y : Space, ‖convYMol L G (t, y)‖ₑ ^ (2 : ℝ))
      ≤ C ^ (2 : ℝ) * ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ) := by
    intro t
    have hGt : AEStronglyMeasurable (fun z : Space => G (t, z)) volume :=
      (hG.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    have hcv : (fun y : Space => convYMol L G (t, y))
        = Sob.cv volume L (fun z : Space => G (t, z)) := by
      funext y
      rw [Sob.cv_apply]
      rfl
    have e := Sob.eLpNorm_cv_le (μ := volume) hL hGt (p := 2) (by norm_num) h2t
    rw [← hcv] at e
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t,
      eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t] at e
    simp only [ENNReal.toReal_ofNat] at e
    exact aux_rpow_sq e
  have hint : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖convYMol L G (t, y)‖ₑ ^ (2 : ℝ))
      ≤ C ^ (2 : ℝ) * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ) := by
    rw [← lintegral_const_mul' _ _ hC2]
    exact lintegral_mono fun t => hpt t
  rw [← hCeq]
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖convYMol L G (t, y)‖ₑ ^ (2 : ℝ))
        ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal P⁻¹ * (C ^ (2 : ℝ) * ∫⁻ t in Ioc (0 : ℝ) P,
            ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ))) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (by gcongr) (by norm_num)
    _ = C * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P,
            ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := aux_outer

/-- Membership and bound for `convYMol L Φ`, `L` continuous with compact support. -/
theorem convY_isInYr_bound {P : ℝ} (L : Space → ℝ) (hL : Continuous L) (hLi : Integrable L volume)
    (Φ : ℝ × Space → CVec3) (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (convYMol L Φ) ∧
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (convYMol L Φ)
        ≤ ENNReal.ofReal (∫ y : Space, |L y|) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 Φ := by
  obtain ⟨G, hG, hΦG⟩ : ∃ G : ℝ × Space → CVec3, StronglyMeasurable G ∧ Φ =ᵐ[volume] G :=
    ⟨hΦ.meas.mk Φ, hΦ.meas.stronglyMeasurable_mk, hΦ.meas.ae_eq_mk⟩
  have hmeasG : StronglyMeasurable (convYMol L G) := by
    have hF : StronglyMeasurable
        (fun p : (ℝ × Space) × Space => L (p.1.2 - p.2) • G (p.1.1, p.2)) := by
      have h1 : StronglyMeasurable (fun p : (ℝ × Space) × Space => L (p.1.2 - p.2)) :=
        (hL.comp ((continuous_snd.comp continuous_fst).sub continuous_snd)).stronglyMeasurable
      have h2 : StronglyMeasurable (fun p : (ℝ × Space) × Space => G (p.1.1, p.2)) :=
        hG.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      exact StronglyMeasurable.smul h1 h2
    exact StronglyMeasurable.integral_prod_right
      (f := fun (x : ℝ × Space) (z : Space) => L (x.2 - z) • G (x.1, z)) hF
  have hae : convYMol L Φ =ᵐ[volume] convYMol L G := by
    have h1 : ∀ᵐ t : ℝ, ∀ᵐ z : Space, Φ (t, z) = G (t, z) :=
      Measure.ae_ae_of_ae_prod hΦG
    refine ae_of_ae_slice (R := fun x : ℝ × Space => convYMol L Φ x = convYMol L G x) ?_
    filter_upwards [h1] with t ht y
    show (∫ z, L (y - z) • Φ (t, z)) = ∫ z, L (y - z) • G (t, z)
    exact integral_congr_ae (ht.mono fun z hz => by simp only [hz])
  have hmeasΦ : AEStronglyMeasurable (convYMol L Φ) volume :=
    hmeasG.aestronglyMeasurable.congr hae.symm
  have hper : ∀ᵐ x : ℝ × Space, convYMol L Φ (x.1 + P, x.2) = convYMol L Φ x := by
    have h1 : ∀ᵐ t : ℝ, ∀ᵐ z : Space, Φ (t + P, z) = Φ (t, z) :=
      Measure.ae_ae_of_ae_prod hΦ.periodic
    refine ae_of_ae_slice (R := fun x : ℝ × Space => convYMol L Φ (x.1 + P, x.2) = convYMol L Φ x) ?_
    filter_upwards [h1] with t ht y
    show (∫ z, L (y - z) • Φ (t + P, z)) = ∫ z, L (y - z) • Φ (t, z)
    exact integral_congr_ae (ht.mono fun z hz => by simp only [hz])
  have hcongrΦ : UnforcedLeray.Short.IIb.phaseLpNorm P 2 Φ
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 G :=
    phaseLpNorm_congr_ae hΦG
  have hcongr : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (convYMol L Φ)
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 (convYMol L G) :=
    phaseLpNorm_congr_ae hae
  have hcore := core_bound (P := P) L hL hLi G hG
  have hfinΦ : UnforcedLeray.Short.IIb.phaseLpNorm P 2 Φ < ⊤ := hΦ.finite
  refine ⟨⟨hper, hmeasΦ, ?_⟩, ?_⟩
  · rw [hcongr]
    refine lt_of_le_of_lt hcore (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    rw [← hcongrΦ]
    exact hfinΦ
  · rw [hcongr, hcongrΦ]
    exact hcore

/-- (2) Young in `y` (source 1351-1362): `convYMol K Φ` and `convDY K j Φ` are members of `Y_2`,
with the stated bound on the first. -/
theorem convYMembership : ConvYMembership := by
  intro P hP K hK hKc Φ hΦ
  have hKcont : Continuous K := hK.continuous
  have hKi : Integrable K volume := hKcont.integrable_of_hasCompactSupport hKc
  obtain ⟨h1, h2⟩ := convY_isInYr_bound K hKcont hKi Φ hΦ
  refine ⟨h1, fun j => ?_, h2⟩
  have hc : Continuous (fderiv ℝ K) := ContDiff.continuous_fderiv hK (by simp)
  have hcont : Continuous (fun w : Space => fderiv ℝ K w (EuclideanSpace.single j (1 : ℝ))) :=
    hc.clm_apply continuous_const
  have hd : HasCompactSupport (fderiv ℝ K) := HasCompactSupport.fderiv ℝ hKc
  have hcpt : HasCompactSupport (fun w : Space => fderiv ℝ K w (EuclideanSpace.single j (1 : ℝ))) :=
    hd.comp_left (g := fun A : Space →L[ℝ] ℝ => A (EuclideanSpace.single j (1 : ℝ))) (by simp)
  have hi : Integrable (fun w : Space => fderiv ℝ K w (EuclideanSpace.single j (1 : ℝ))) volume :=
    hcont.integrable_of_hasCompactSupport hcpt
  exact (convY_isInYr_bound _ hcont hi Φ hΦ).1

end UnforcedLeray.Short.PartIIIb.Concrete
