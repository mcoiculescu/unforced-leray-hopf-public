import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.PhaseIBP

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

lemma int_rpow_bound (b δ E : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hδ : 1 ≤ δ) (hE : 0 < E) :
    ∫ l in Ioc (0 : ℝ) b, E * l ^ (δ - 1) ≤ E := by
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hb0.le,
    integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (δ - 1 + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, sub_zero]
  have hb : b ^ (δ - 1 + 1) ≤ 1 := Real.rpow_le_one hb0.le hb1.le (by linarith)
  have : b ^ (δ - 1 + 1) / (δ - 1 + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  nlinarith

lemma finite_b_bound (hP : PhaseIBP) (ω : ℝ → ℂ) (δ E : ℝ) (hδ : 1 ≤ δ) (hE : 0 < E)
    (hω : ContDiffOn ℝ 1 ω (Ioo 0 1))
    (h1 : ∀ l ∈ Ioo (0 : ℝ) 1, ‖ω l‖ ≤ E * l ^ (δ - 1))
    (h2 : ∀ l ∈ Ioo (0 : ℝ) 1, ‖ω l + (l : ℂ) * deriv ω l‖ ≤ E * l ^ (δ - 1))
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (f : ℝ → ℝ) (hfm : Measurable f)
    (hper : ∀ q, f (q + c) = f q) (hint : IntervalIntegrable f volume 0 c)
    (hmean : (∫ q in (0 : ℝ)..c, f q) = 0) (q₀ : ℝ) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ‖∫ l in Ioc (0 : ℝ) b, ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ ≤
      2 * ε * E * ∫ q in (0 : ℝ)..c, |f q| := by
  have hsub : ∀ l ∈ Ioc (0 : ℝ) b, l ∈ Ioo (0 : ℝ) 1 := fun l hl => ⟨hl.1, lt_of_le_of_lt hl.2 hb1⟩
  have := hP ε hε c hc f hfm hper hint hmean q₀ ω b δ E hb0 hb1 (by linarith) hE.le hω
    (fun l hl => h1 l (hsub l hl)) (fun l hl => h2 l (hsub l hl))
  refine this.trans ?_
  have hA0 : 0 ≤ ∫ q in (0 : ℝ)..c, |f q| :=
    intervalIntegral.integral_nonneg hc.le (fun _ _ => abs_nonneg _)
  have hV : ContinuousOn (fun l => ‖ω l + (l : ℂ) * deriv ω l‖) (Ioo 0 1) := by
    have hd : ContinuousOn (deriv ω) (Ioo 0 1) := hω.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    exact (hω.continuousOn.add (Complex.continuous_ofReal.continuousOn.mul hd)).norm
  have hI : IntegrableOn (fun l => ‖ω l + (l : ℂ) * deriv ω l‖) (Ioc 0 b) :=
    phaseIBP_int_of_bound b δ E hb0 hb1 (by linarith) _ hV
      (fun l hl => by rw [abs_of_nonneg (norm_nonneg _)]; exact h2 l (hsub l hl))
  have hI' : IntegrableOn (fun l : ℝ => E * l ^ (δ - 1)) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le).1
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < δ - 1)).const_mul E)
  have hint2 : ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖ ≤ E :=
    (setIntegral_mono_on hI hI' measurableSet_Ioc (fun l hl => h2 l (hsub l hl))).trans
      (int_rpow_bound b δ E hb0 hb1 hδ hE)
  have hbω : b * ‖ω b‖ ≤ E := by
    have := h1 b ⟨hb0, hb1⟩
    have e : b * b ^ (δ - 1) = b ^ δ := by
      rw [Real.rpow_sub_one hb0.ne']; field_simp
    have hbd : b ^ δ ≤ 1 := Real.rpow_le_one hb0.le hb1.le (by linarith)
    calc b * ‖ω b‖ ≤ b * (E * b ^ (δ - 1)) := mul_le_mul_of_nonneg_left this hb0.le
      _ = E * b ^ δ := by rw [← e]; ring
      _ ≤ E * 1 := mul_le_mul_of_nonneg_left hbd hE.le
      _ = E := mul_one E
  have : ε * (∫ q in (0 : ℝ)..c, |f q|) * (b * ‖ω b‖ + ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖) ≤
      ε * (∫ q in (0 : ℝ)..c, |f q|) * (E + E) :=
    mul_le_mul_of_nonneg_left (add_le_add hbω hint2) (mul_nonneg hε.le hA0)
  linarith

theorem osc_abstract (hP : PhaseIBP) (ω : ℝ → ℂ) (δ E : ℝ) (hδ : 1 ≤ δ) (hE : 0 < E)
    (hω : ContDiffOn ℝ 1 ω (Ioo 0 1))
    (h1 : ∀ l ∈ Ioo (0 : ℝ) 1, ‖ω l‖ ≤ E * l ^ (δ - 1))
    (h2 : ∀ l ∈ Ioo (0 : ℝ) 1, ‖ω l + (l : ℂ) * deriv ω l‖ ≤ E * l ^ (δ - 1))
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (f : ℝ → ℝ) (hfm : Measurable f)
    (hper : ∀ q, f (q + c) = f q) (hmean : (∫ q in Ioc 0 c, f q) = 0) (q₀ : ℝ) :
    ‖∫ l in Ioo (0 : ℝ) 1, ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (2 * ε * E) * ∫⁻ q in Ioc 0 c, ‖f q‖ₑ := by
  by_cases hA : ∫⁻ q in Ioc 0 c, ‖f q‖ₑ = ⊤
  · rw [hA, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hfi : IntegrableOn f (Ioc 0 c) :=
    ⟨hfm.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 (lt_top_iff_ne_top.2 hA)⟩
  have hint : IntervalIntegrable f volume 0 c :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).2 hfi
  have hmean' : (∫ q in (0 : ℝ)..c, f q) = 0 := by
    rw [intervalIntegral.integral_of_le hc.le]; exact hmean
  have hA0 : 0 ≤ ∫ q in (0 : ℝ)..c, |f q| :=
    intervalIntegral.integral_nonneg hc.le (fun _ _ => abs_nonneg _)
  set G : ℝ → ℂ := fun l => ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ) with hG
  have key : ‖∫ l in Ioo (0 : ℝ) 1, G l‖ ≤ 2 * ε * E * ∫ q in (0 : ℝ)..c, |f q| := by
    by_cases hGi : IntegrableOn G (Ioo 0 1)
    · set s : ℕ → Set ℝ := fun n => Ioc 0 (1 - 1 / ((n : ℝ) + 2)) with hs
      have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioc
      have hmono : Monotone s := by
        intro m n hmn
        apply Ioc_subset_Ioc_right
        have : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (m : ℝ) ≤ n := by exact_mod_cast hmn
          linarith
        linarith
      have hU : (⋃ n, s n) = Ioo 0 1 := by
        ext x
        simp only [mem_iUnion, hs, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨n, h0, h1⟩
          refine ⟨h0, lt_of_le_of_lt h1 ?_⟩
          have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
          linarith
        · rintro ⟨h0, h1⟩
          obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - x))
          refine ⟨n, h0, ?_⟩
          have hpos : 0 < 1 - x := by linarith
          have : 1 / ((n : ℝ) + 2) ≤ 1 - x := by
            rw [div_le_iff₀ (by positivity)]
            have := (div_lt_iff₀ hpos).1 hn
            nlinarith
          linarith
      have ht := tendsto_setIntegral_of_monotone hsm hmono (by rw [hU]; exact hGi)
      rw [hU] at ht
      refine le_of_tendsto' ht.norm (fun n => ?_)
      have hb0 : (0 : ℝ) < 1 - 1 / ((n : ℝ) + 2) := by
        have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith
      have hb1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
      exact finite_b_bound hP ω δ E hδ hE hω h1 h2 ε c hε hc f hfm hper hint hmean' q₀ _ hb0 hb1
    · rw [integral_undef hGi, norm_zero]
      positivity
  have hAe : ENNReal.ofReal (∫ q in (0 : ℝ)..c, |f q|) = ∫⁻ q in Ioc 0 c, ‖f q‖ₑ := by
    simp only [← Real.norm_eq_abs]
    rw [intervalIntegral.integral_of_le hc.le,
      ofReal_integral_eq_lintegral_ofReal hfi.norm (Eventually.of_forall fun _ => norm_nonneg _)]
    refine lintegral_congr (fun q => ?_)
    simp [Real.enorm_eq_ofReal_abs]
  calc ‖∫ l in Ioo (0 : ℝ) 1, G l‖ₑ = ENNReal.ofReal ‖∫ l in Ioo (0 : ℝ) 1, G l‖ :=
        (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal (2 * ε * E * ∫ q in (0 : ℝ)..c, |f q|) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (2 * ε * E) * ENNReal.ofReal (∫ q in (0 : ℝ)..c, |f q|) :=
        ENNReal.ofReal_mul (by positivity)
    _ = _ := by rw [hAe]

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
