import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# Young's inequality for the dilated positive kernel (source 4001-4002)

Proves `youngDilated_holds : YoungDilated` (defined in `Sub/PositiveKernel.lean`).
The route: dilation `∫ K(l z) dz = l^{-3} ∫ K`, translation invariance, Cauchy-Schwarz
against the probability-free measure `k(y - l·) dz`, then Tonelli.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- Dilation of a lower Lebesgue integral on `ℝ³`: `∫ K(l z) dz = l^{-3} ∫ K`. -/
private lemma yd_dil (l : ℝ) (hl : 0 < l) (K : UnforcedLeray.Space → ℝ≥0∞) (hK : Measurable K) :
    ∫⁻ z, K (l • z) = ENNReal.ofReal (l ^ (-3 : ℝ)) * ∫⁻ w, K w := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure UnforcedLeray.Space)) hl.ne'
  have hm : Measurable (fun z : UnforcedLeray.Space => l • z) :=
    (continuous_const_smul l).measurable
  have h1 : ∫⁻ z, K (l • z) =
      ∫⁻ w, K w ∂(Measure.map (fun z : UnforcedLeray.Space => l • z) volume) :=
    (lintegral_map hK hm).symm
  rw [h1, hmap, lintegral_smul_measure, finrank_euclideanSpace_fin]
  congr 1
  rw [show (l ^ (-3 : ℝ)) = (l ^ 3)⁻¹ by
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hl.le, Real.rpow_natCast]]
  rw [abs_of_nonneg (by positivity)]

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`. -/
private lemma yd_sq_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- **Young for the dilated positive kernel** (source 4001-4002). -/
theorem youngDilated_holds : YoungDilated := by
  intro k g hk hg A hA l hl
  -- the mass of `k(y - l·)` in `z` is `l^{-3} ∫ k`, independent of `y`
  have hm : ∀ y : UnforcedLeray.Space,
      ∫⁻ z, k (y - l • z) = ENNReal.ofReal (l ^ (-3 : ℝ)) * ∫⁻ x, k x := by
    intro y
    have hk' : Measurable (fun w : UnforcedLeray.Space => k (y - w)) :=
      hk.comp (measurable_const.sub measurable_id)
    have := yd_dil l hl (fun w => k (y - w)) hk'
    rw [this, lintegral_sub_left_eq_self k y]
  -- pointwise Cauchy-Schwarz in the form (∫ f g)^2 ≤ (∫ f)(∫ f g^2) for f = k(y - l·)
  have CS : ∀ y : UnforcedLeray.Space,
      (∫⁻ z, k (y - l • z) * g z) ^ (2 : ℝ) ≤
        (∫⁻ z, k (y - l • z)) * ∫⁻ z, k (y - l • z) * g z ^ (2 : ℝ) := by
    intro y
    have hf : Measurable (fun z : UnforcedLeray.Space => k (y - l • z)) :=
      hk.comp (measurable_const.sub (continuous_const_smul l).measurable)
    have h1 : ∫⁻ z, k (y - l • z) * g z =
        ∫⁻ z, g z ∂((volume : Measure UnforcedLeray.Space).withDensity
          (fun z => k (y - l • z))) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
      rfl
    have h2 : ∫⁻ z, k (y - l • z) * g z ^ (2 : ℝ) =
        ∫⁻ z, g z ^ (2 : ℝ) ∂((volume : Measure UnforcedLeray.Space).withDensity
          (fun z => k (y - l • z))) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hf (hg.pow_const _)]
      rfl
    have h3 : ∫⁻ z, k (y - l • z) = ∫⁻ z, (1 : ℝ≥0∞) ∂((volume : Measure UnforcedLeray.Space).withDensity
          (fun z => k (y - l • z))) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hf measurable_const]
      simp
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq
      ((volume : Measure UnforcedLeray.Space).withDensity (fun z => k (y - l • z)))
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := g) aemeasurable_const hg.aemeasurable
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow] at hH
    rw [h1, h2, h3]
    calc (∫⁻ z, g z ∂((volume : Measure UnforcedLeray.Space).withDensity
            (fun z => k (y - l • z)))) ^ (2 : ℝ)
        ≤ ((∫⁻ z, (1 : ℝ≥0∞) ∂((volume : Measure UnforcedLeray.Space).withDensity
            (fun z => k (y - l • z)))) ^ (1 / 2 : ℝ) *
          (∫⁻ z, g z ^ (2 : ℝ) ∂((volume : Measure UnforcedLeray.Space).withDensity
            (fun z => k (y - l • z)))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hH (by norm_num)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), yd_sq_half, yd_sq_half]
  -- Tonelli for the integral of the square
  have hmeasF : Measurable (Function.uncurry fun (y z : UnforcedLeray.Space) =>
      k (y - l • z) * g z ^ (2 : ℝ)) := by
    have h1 : Measurable (fun p : UnforcedLeray.Space × UnforcedLeray.Space => k (p.1 - l • p.2)) :=
      hk.comp (measurable_fst.sub ((continuous_const_smul l).measurable.comp measurable_snd))
    exact h1.mul ((hg.comp measurable_snd).pow_const _)
  have hI : Measurable fun y : UnforcedLeray.Space => ∫⁻ z, k (y - l • z) * g z ^ (2 : ℝ) :=
    hmeasF.lintegral_prod_right
  have hswap : ∫⁻ y, ∫⁻ z, k (y - l • z) * g z ^ (2 : ℝ) =
      ∫⁻ z, ∫⁻ y, k (y - l • z) * g z ^ (2 : ℝ) := by
    exact lintegral_lintegral_swap hmeasF.aemeasurable
  have hinner : ∀ z : UnforcedLeray.Space,
      ∫⁻ y, k (y - l • z) * g z ^ (2 : ℝ) = (∫⁻ x, k x) * g z ^ (2 : ℝ) := by
    intro z
    have hf : Measurable fun y : UnforcedLeray.Space => k (y - l • z) :=
      hk.comp (measurable_id.sub_const _)
    rw [lintegral_mul_const _ hf, lintegral_sub_right_eq_self k]
  have hG : Measurable fun z : UnforcedLeray.Space => g z ^ (2 : ℝ) := hg.pow_const _
  -- the integral of the square
  have hint : ∫⁻ y, (∫⁻ z, k (y - l • z) * g z) ^ (2 : ℝ) ≤
      ENNReal.ofReal (l ^ (-3 : ℝ)) * (∫⁻ x, k x) * ((∫⁻ x, k x) * ∫⁻ z, g z ^ (2 : ℝ)) := by
    calc ∫⁻ y, (∫⁻ z, k (y - l • z) * g z) ^ (2 : ℝ)
        ≤ ∫⁻ y, (ENNReal.ofReal (l ^ (-3 : ℝ)) * (∫⁻ x, k x)) *
            ∫⁻ z, k (y - l • z) * g z ^ (2 : ℝ) := by
          refine lintegral_mono fun y => ?_
          rw [← hm y]
          exact CS y
      _ = ENNReal.ofReal (l ^ (-3 : ℝ)) * (∫⁻ x, k x) *
            ∫⁻ y, ∫⁻ z, k (y - l • z) * g z ^ (2 : ℝ) := by
          rw [lintegral_const_mul _ hI]
      _ = ENNReal.ofReal (l ^ (-3 : ℝ)) * (∫⁻ x, k x) *
            ∫⁻ z, ∫⁻ y, k (y - l • z) * g z ^ (2 : ℝ) := by rw [hswap]
      _ = ENNReal.ofReal (l ^ (-3 : ℝ)) * (∫⁻ x, k x) *
            ∫⁻ z, (∫⁻ x, k x) * g z ^ (2 : ℝ) := by
          congr 1
          exact lintegral_congr fun z => hinner z
      _ = ENNReal.ofReal (l ^ (-3 : ℝ)) * (∫⁻ x, k x) *
            ((∫⁻ x, k x) * ∫⁻ z, g z ^ (2 : ℝ)) := by
          rw [lintegral_const_mul _ hG]
  -- compare with the target
  set G : ℝ≥0∞ := ∫⁻ z, g z ^ (2 : ℝ) with hGdef
  set X : ℝ≥0∞ := ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A * G ^ (1 / 2 : ℝ) with hXdef
  have hX2 : X ^ (2 : ℝ) = ENNReal.ofReal (l ^ (-3 : ℝ)) * A * (A * G) := by
    rw [hXdef, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), yd_sq_half,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    rw [← Real.rpow_mul hl.le]
    norm_num
    ring
  have hbound : ∫⁻ y, (∫⁻ z, k (y - l • z) * g z) ^ (2 : ℝ) ≤ X ^ (2 : ℝ) := by
    rw [hX2]
    refine hint.trans ?_
    gcongr
  calc (∫⁻ y : UnforcedLeray.Space,
          (∫⁻ z : UnforcedLeray.Space, k (y - l • z) * g z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (X ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = X := by rw [← ENNReal.rpow_mul]; norm_num

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
