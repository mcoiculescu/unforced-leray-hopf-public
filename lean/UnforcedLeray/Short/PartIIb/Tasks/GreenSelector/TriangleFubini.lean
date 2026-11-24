import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.TriangleFubini.Tri

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

open PartIIbF4Aux TriFubiniAux

theorem propagatorTriangleFubini_proof : UnforcedLeray.Short.IIb.PropagatorTriangleFubini := by
  intro m _hm p U M_U hc hH hM hU hbd φ C_φ L hφ hC hL f hf s hs
  have hsH : s ≤ p.H := hs.2
  have hs0 : 0 ≤ s := hs.1
  set μ : Measure ℝ := volume.restrict (Ioc 0 s) with hμ
  have hfs : IntegrableOn f (Ioc 0 s) volume := hf.mono_set (Ioc_subset_Ioc_right hsH)
  have hmeas : ∀ a : ℝ, 0 ≤ a → a ≤ s → ∀ x : Xmc p.c m,
      AEStronglyMeasurable (fun r => L r (U r a x)) (volume.restrict (Ioc a s)) := by
    intro a ha has x
    have hti := (hU.timeIntegrable φ hφ a s ha has hsH x)
    have hti' := (intervalIntegrable_iff_integrableOn_Ioc_of_le has).1 hti
    refine hti'.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
    have hrI : r ∈ Icc 0 p.H := ⟨ha.trans hr.1.le, hr.2.trans hsH⟩
    exact ((hL r hrI).2 (U r a x)).2.symm
  have hmeasK := aesm_triangle (H := p.H) (M_U := M_U) U L s hs0 hsH hU.id_self hU.comp_cocycle
    hU.strongCont hbd hmeas f hfs.1
  set K : ℝ × ℝ → ℝ := fun q => (Ioi q.2).indicator (fun r => L r (U r q.2 (f q.2))) q.1 with hK
  have hKint : Integrable K (μ.prod μ) := by
    have hb : Integrable (fun q : ℝ × ℝ => (C_φ * M_U) * (1 * ‖f q.2‖)) (μ.prod μ) := by
      have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
        integrableOn_const (by simp)
      exact (h1.mul_prod hfs.norm).const_mul _
    refine hb.mono' hmeasK ?_
    have hr1 : ∀ᵐ q ∂(μ.prod μ), q.1 ∈ Ioc 0 s :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hr2 : ∀ᵐ q ∂(μ.prod μ), q.2 ∈ Ioc 0 s :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hr1, hr2] with q hq1 hq2
    obtain ⟨r, t⟩ := q
    simp only at hq1 hq2 ⊢
    by_cases hrt : t < r
    · rw [hK]
      simp only [Set.indicator_of_mem (show r ∈ Ioi t from hrt)]
      have hrI : r ∈ Icc 0 p.H := ⟨hq1.1.le, hq1.2.trans hsH⟩
      calc ‖L r (U r t (f t))‖ ≤ ‖L r‖ * ‖U r t (f t)‖ := (L r).le_opNorm _
        _ ≤ C_φ * (M_U * ‖f t‖) := by
          refine mul_le_mul ((hL r hrI).1) ?_ (norm_nonneg _) hC
          calc ‖U r t (f t)‖ ≤ ‖U r t‖ * ‖f t‖ := (U r t).le_opNorm _
            _ ≤ M_U * ‖f t‖ :=
              mul_le_mul_of_nonneg_right (hbd t r hq2.1.le hrt.le (hq1.2.trans hsH)) (norm_nonneg _)
        _ = C_φ * M_U * (1 * ‖f t‖) := by ring
    · rw [hK]
      simp only [Set.indicator_of_notMem (show r ∉ Ioi t from hrt), norm_zero]
      positivity
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun r t => K (r, t)) hKint
  -- identify the inner integrals
  have hinner_r : ∀ r ∈ Ioc 0 s, (∫ t in Ioc 0 r, L r (U r t (f t))) = ∫ t, K (r, t) ∂μ := by
    intro r hr
    have h1 : ∀ t, K (r, t) = (Iio r).indicator (fun t => L r (U r t (f t))) t := by
      intro t
      simp only [hK]
      by_cases h : t < r
      · rw [Set.indicator_of_mem (show r ∈ Ioi t from h), Set.indicator_of_mem (show t ∈ Iio r from h)]
      · rw [Set.indicator_of_notMem (show r ∉ Ioi t from h),
          Set.indicator_of_notMem (show t ∉ Iio r from h)]
    simp_rw [h1]
    rw [hμ, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have : Iio r ∩ Ioc 0 s = Ioo 0 r := by
      ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans hr.2⟩
    rw [this, integral_Ioc_eq_integral_Ioo]
  have hinner_t : ∀ t ∈ Ioc 0 s, (∫ r in Ioc t s, L r (U r t (f t))) = ∫ r, K (r, t) ∂μ := by
    intro t ht
    simp only [hK]
    rw [hμ, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have : Ioi t ∩ Ioc 0 s = Ioc t s := by
      ext r; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, ht.1.trans h1, h3⟩
    rw [this]
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs0]
    have := hKint.integral_prod_left
    exact this.congr ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun r hr => (hinner_r r hr).symm))
  · have e1 : (∫ t in Ioc 0 s, ∫ r in Ioc t s, L r (U r t (f t))) = ∫ t, ∫ r, K (r, t) ∂μ ∂μ :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => hinner_t t ht
    have e2 : (∫ r in Ioc 0 s, ∫ t in Ioc 0 r, L r (U r t (f t))) = ∫ r, ∫ t, K (r, t) ∂μ ∂μ :=
      setIntegral_congr_fun measurableSet_Ioc fun r hr => hinner_r r hr
    rw [e1, e2]
    exact hswap.symm

end UnforcedLeray.Short.IIb
