import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUSourceTNorm` (item `PartIII-b:C/near/delta/9/1/11`)

Source 3564-3568: for `W ≥ 1` (`m_Z ≥ 0`) and `ρ_b ≤ 1`, the meridional block of `F₁ + F₂` has
`𝒯`-norm at most `‖F‖_𝒵 = ‖F₁‖_{𝒵₁} + ‖F₂‖_{ρ_b^{-1/2}𝒯}`.

Pointwise, the meridional block of a `3×3` tensor `T` has Frobenius square
`T₀₀² + 2 ((T₀₂+T₂₀)/2)² + T₂₂² ≤ ∑ T_{ab}²` (convexity of the square), so
`‖merBlockC T p‖ ≤ ‖T p‖`.  Then Minkowski in `L²(s^{-1/2}ds dς)` with the measure comparisons
`s^{-1/2}dς ≤ W² s^{-1/2}dς` (`W ≥ 1`) and `s^{-1/2}dς ≤ ρ_b^{-1} s^{-1/2}dς` (`ρ_b ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

/-- Pointwise Frobenius bound of the meridional block. -/
theorem fu_merBlock_tnorm_le (T : Ten3) :
    UnforcedLeray.Short.IIIa.tnorm2 (fun i j => ((nsSym T (merIdx i) (merIdx j) : ℝ) : ℂ))
      ≤ ‖T‖ := by
  unfold UnforcedLeray.Short.IIIa.tnorm2
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have key : ∀ a b : ℝ, 2 * ((a + b) / 2) ^ 2 ≤ a ^ 2 + b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have hL : ∑ i : Fin 2, ∑ j : Fin 2, ‖((nsSym T (merIdx i) (merIdx j) : ℝ) : ℂ)‖ ^ 2
      = T (0, 0) ^ 2 + 2 * ((T (0, 2) + T (2, 0)) / 2) ^ 2 + T (2, 2) ^ 2 := by
    simp [Fin.sum_univ_two, merIdx, nsSym, symRZ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hL]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [key (T (0, 2)) (T (2, 0)), sq_nonneg (T (0, 1)), sq_nonneg (T (1, 0)),
    sq_nonneg (T (1, 1)), sq_nonneg (T (1, 2)), sq_nonneg (T (2, 1))]

theorem fu_tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) :
    0 ≤ UnforcedLeray.Short.IIIa.tnorm2 T := by
  unfold UnforcedLeray.Short.IIIa.tnorm2
  exact Real.sqrt_nonneg _

/-- **Source 3564-3568**: `‖F₁ + F₂‖_𝒯 ≤ ‖F‖_𝒵` for `W ≥ 1` and `ρ_b ≤ 1`. -/
theorem fuSourceTNorm : FUSourceTNorm := by
  intro c mZ ρb hc hmZ hρ hρ1 F
  -- the weight is at least one
  have hW1 : ∀ p : Chart, 1 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := fun p => by
    unfold UnforcedLeray.Short.IIIa.transWeight
    exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (div_nonneg hmZ zero_le_two)
  -- measure comparisons
  have hAZ : ageμ c (-1 / 2) ≤ z1Measure c mZ := by
    refine Measure.le_iff.2 fun s hs => ?_
    unfold z1Measure
    rw [withDensity_apply _ hs]
    calc ageμ c (-1 / 2) s = ∫⁻ _ in s, 1 ∂(ageμ c (-1 / 2)) := (setLIntegral_one s).symm
      _ ≤ ∫⁻ a in s, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ a ^ 2)
            ∂(ageμ c (-1 / 2)) :=
          lintegral_mono fun a => ENNReal.one_le_ofReal.2 (one_le_pow₀ (hW1 a))
  have hAH : ageμ c (-1 / 2) ≤ htRhoMeasure c ρb := by
    refine Measure.le_iff'.2 fun s => ?_
    unfold htRhoMeasure
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left zero_le
      (ENNReal.one_le_ofReal.2 ((one_le_inv₀ hρ).2 hρ1))
  -- absolute continuity for the measurability transfer
  have hAc1 : ageμ c (-1 / 2) ≪ z1Measure c mZ :=
    FlatSettingInst.ageμ_ac_z1Measure c mZ
  have hAc2 : ageμ c (-1 / 2) ≪ htRhoMeasure c ρb := Measure.absolutelyContinuous_of_le hAH
  have hm1 : AEStronglyMeasurable (fun p => ‖(F.fst : Chart → Ten3) p‖) (ageμ c (-1 / 2)) :=
    ((Lp.aestronglyMeasurable F.fst).norm).mono_ac hAc1
  have hm2 : AEStronglyMeasurable (fun p => ‖(F.snd : Chart → Ten3) p‖) (ageμ c (-1 / 2)) :=
    ((Lp.aestronglyMeasurable F.snd).norm).mono_ac hAc2
  -- pointwise bound
  have hpt : ∀ p : Chart, UnforcedLeray.Short.IIIa.tnorm2 (merBlockC (zsum F) p)
      ≤ ‖(F.fst : Chart → Ten3) p‖ + ‖(F.snd : Chart → Ten3) p‖ := by
    intro p
    exact (fu_merBlock_tnorm_le ((F.fst : Chart → Ten3) p + (F.snd : Chart → Ten3) p)).trans
      (norm_add_le _ _)
  have hT : UnforcedLeray.Short.IIIa.tCalNorm c (merBlockC (zsum F))
      ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2))
        + eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) := by
    unfold UnforcedLeray.Short.IIIa.tCalNorm
    calc eLpNorm (fun p => UnforcedLeray.Short.IIIa.tnorm2 (merBlockC (zsum F) p)) 2
          (ageμ c (-1 / 2))
        ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖ + ‖(F.snd : Chart → Ten3) p‖) 2
            (ageμ c (-1 / 2)) := by
          refine eLpNorm_mono_real fun p => ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (fu_tnorm2_nonneg _)]
          exact hpt p
      _ ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2))
            + eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) :=
          eLpNorm_add_le hm1 hm2 (by norm_num)
  -- the two component norms
  have hF1 : eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (z1Measure c mZ)
      = ENNReal.ofReal ‖F.fst‖ := by
    rw [eLpNorm_norm, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F.fst)]
  have hF2 : eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (htRhoMeasure c ρb)
      = ENNReal.ofReal ‖F.snd‖ := by
    rw [eLpNorm_norm, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F.snd)]
  have hn : ‖F‖ = ‖F.fst‖ + ‖F.snd‖ := by
    rw [WithLp.prod_norm_eq_add (by norm_num)]
    simp
  calc UnforcedLeray.Short.IIIa.tCalNorm c (merBlockC (zsum F))
      ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2))
        + eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) := hT
    _ ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (z1Measure c mZ)
        + eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (htRhoMeasure c ρb) :=
          add_le_add (eLpNorm_mono_measure _ hAZ) (eLpNorm_mono_measure _ hAH)
    _ = ENNReal.ofReal ‖F.fst‖ + ENNReal.ofReal ‖F.snd‖ := by rw [hF1, hF2]
    _ = ENNReal.ofReal (‖F.fst‖ + ‖F.snd‖) :=
          (ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)).symm
    _ = ENNReal.ofReal ‖F‖ := by rw [hn]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
