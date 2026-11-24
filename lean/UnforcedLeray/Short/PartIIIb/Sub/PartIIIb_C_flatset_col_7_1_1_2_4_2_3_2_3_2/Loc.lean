import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Integ

/-!
# Local integrability of `s ↦ s^(-3/2) ∫_strip ⟨∇ψ, b_s⟩` (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The indicator-truncated pairing integrand on the profile space. -/
def hj3Xi (c a b R : ℝ) (β : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (ψ : ℝ × ℝ → ℝ) (p : UnforcedLeray.B0220.Profile) : ℂ :=
  (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R)).indicator
      (fun p => ((UnforcedLeray.B0579.pd 0 ψ p.2 : ℝ) : ℂ) *
        (EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ) (β p)) p +
  (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R)).indicator
      (fun p => ((UnforcedLeray.B0579.pd 1 ψ p.2 : ℝ) : ℂ) *
        (EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ) (β p)) p

theorem hj3Xi_integrable {c a b R : ℝ} {ψ : ℝ × ℝ → ℝ} (hc : 0 < c) (ha : 0 < a)
    (hψ : UnforcedLeray.B0579.IsCylTest c ψ)
    {β : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC}
    (hβ : MemLp β 2 (UnforcedLeray.B0220.measureH c)) :
    Integrable (hj3Xi c a b R β ψ) (UnforcedLeray.B0220.measureH c) :=
  (hj3_integrable_band hβ ha (hj3_pd_continuous hψ 0) 0).add
    (hj3_integrable_band hβ ha (hj3_pd_continuous hψ 1) 1)

theorem hj3_pointwise {c R : ℝ} {ψ : ℝ × ℝ → ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0)
    (β : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) {a b : ℝ} {s : ℝ}
    (hs : s ∈ Icc a b) {x : ℝ × ℝ} (hx : x ∈ Ioc 0 c ×ˢ (univ : Set ℝ)) :
    hj3Xi c a b R β ψ (s, x) =
      (β (s, x) 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
        β (s, x) 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)) := by
  unfold hj3Xi
  by_cases hf : R < |x.2|
  · have h0 := hj3_pd_eq_zero_of_far hR 0 x hf
    have h1 := hj3_pd_eq_zero_of_far hR 1 x hf
    have hnot : (s, x) ∉ Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R) := fun hmem =>
      absurd (abs_le.2 hmem.2.2) (not_le.2 hf)
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot, h0, h1]
    simp
  · push_neg at hf
    have hmem : (s, x) ∈ Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R) :=
      mk_mem_prod hs (mk_mem_prod ⟨hx.1.1.le, hx.1.2⟩ ⟨(abs_le.1 hf).1, (abs_le.1 hf).2⟩)
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    simp [EuclideanSpace.proj]
    ring

/-- The slice pairing `s ↦ s^(-3/2) ∫_strip ⟨∇ψ, b_s⟩` is locally integrable on `(0,∞)`. -/
theorem hj3_loc_int {c : ℝ} (hc : 0 < c)
    (b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    LocallyIntegrableOn (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in stripSet c,
          ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
              ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
            (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
              ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)))
      (Ioi 0) := by
  obtain ⟨R, hR⟩ := hψ.band
  have hβ : MemLp (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      2 (UnforcedLeray.B0220.measureH c) := Lp.memLp b
  have hlt : ∀ᵐ p ∂UnforcedLeray.B0220.cellMeasure c, UnforcedLeray.B0220.weightH p < ∞ :=
    Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  -- integrability of `F` on each compact interval in `(0, ∞)`
  have hint : ∀ a t : ℝ, 0 < a → IntegrableOn (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in stripSet c,
          ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
              ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
            (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
              ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))) (Icc a t) := by
    intro a t ha
    have hW := (integrable_withDensity_iff_integrable_smul'
        UnforcedLeray.B0220.measurable_weightH hlt).1
      (hj3Xi_integrable (b := t) (R := R) hc ha hψ hβ)
    rw [UnforcedLeray.B0224.cellMeasure_eq_prod' c] at hW
    have hG := hW.integral_prod_left
    have hGI : IntegrableOn (fun s : ℝ => ∫ x, (UnforcedLeray.B0220.weightH (s, x)).toReal •
        hj3Xi c a t R (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) ψ (s, x)
          ∂(volume.restrict (UnforcedLeray.B0224.strip c))) (Icc a t) := by
      have hsub : Icc a t ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le ha hs.1
      exact hG.mono_measure (Measure.restrict_mono hsub le_rfl)
    refine hGI.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le ha hs.1
    have hw : ∀ x : ℝ × ℝ, (UnforcedLeray.B0220.weightH (s, x)).toReal = s ^ (-(3 / 2 : ℝ)) := by
      intro x
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg hs0.le _)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (UnforcedLeray.B0224.measurableSet_strip c)] with x hx
    rw [hw x, Complex.real_smul, hj3_pointwise hR _ hs hx]
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkc
  obtain ⟨a, t, ha, hkab⟩ := hj3_pos_bound hkc hk
  exact (hint a t ha).mono_set hkab

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
