import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.BandVanish

/-!
# `L¹` of the densities on a band (source 3511-3514, 4464-4467, 4610)

On a band `[s₁,s₂] × cell` with `s₁ > 0`, `energyLoc` gives a finite `L²` norm of `b` (through
`vnorm2`), and `f` is `L²` on the same set by the sixth clause of `VtvHyps`.  Both are `L¹` on the
finite-measure set `[s₁,s₂] × box`, and Fubini gives that `s ↦ ∫_box (‖b₀‖+‖b₁‖)(s,·)` and the
same for `f` are integrable on `[s₁,s₂]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- A component is bounded by the Euclidean-type norm `vnorm2`. -/
theorem vtvBandL1_sq_le_vnorm2 (a : Fin 2 → ℂ) (i : Fin 2) :
    ‖a i‖ ^ 2 ≤ UnforcedLeray.Short.IIIa.vnorm2 a ^ 2 := by
  unfold UnforcedLeray.Short.IIIa.vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  exact Finset.single_le_sum (f := fun j => ‖a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem vtvBandL1 : VtvBandL1 := by
  intro ν c μ tr ω g b G f H s₁ s₂ R hs₁
  by_cases hlt : s₁ < s₂
  · have hE := H.2.2.2.1.energyLoc s₁ s₂ hs₁ hlt
    have hf := H.2.2.2.2.2.1 s₁ s₂ hs₁
    have hprod : (volume.restrict (Icc s₁ s₂)).prod (volume.restrict (vtvBox c R))
        = volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R) :=
      Measure.prod_restrict _ _
    have hfinS : volume (Icc s₁ s₂ ×ˢ vtvBox c R) < ⊤ := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Icc_lt_top (volume_vtvBox_lt_top c R)
    haveI : IsFiniteMeasure (volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfinS⟩
    -- squares of the components of `b` are integrable on the band box
    have hbsq : ∀ i : Fin 2, Integrable (fun p : ℝ × (ℝ × ℝ) => ‖b p i‖ ^ 2)
        (volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R)) := by
      intro i
      refine ⟨((H.2.2.2.1.measurable i).norm.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun p => (sq_nonneg ‖b p i‖ : (0 : ℝ) ≤ ‖b p i‖ ^ 2))]
      have h1 : ∫⁻ p in Icc s₁ s₂ ×ˢ vtvBox c R, ENNReal.ofReal (‖b p i‖ ^ 2)
          ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ vtvBox c R,
              ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2
                + UnforcedLeray.Short.IIIa.tnorm2 (G p) ^ 2) := by
        refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
        linarith [vtvBandL1_sq_le_vnorm2 (b p) i,
          sq_nonneg (UnforcedLeray.Short.IIIa.tnorm2 (G p))]
      have h2 : ∫⁻ p in Icc s₁ s₂ ×ˢ vtvBox c R,
              ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2
                + UnforcedLeray.Short.IIIa.tnorm2 (G p) ^ 2)
          ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
              ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2
                + UnforcedLeray.Short.IIIa.tnorm2 (G p) ^ 2) :=
        lintegral_mono_set (Set.prod_mono subset_rfl (vtvBox_subset_cell c R))
      exact lt_of_le_of_lt (h1.trans h2) hE
    -- the components of `b` are `L¹` on the band box
    have hbi : ∀ i : Fin 2, Integrable (fun p : ℝ × (ℝ × ℝ) => ‖b p i‖)
        (volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R)) := by
      intro i
      have hone : Integrable (fun _ : ℝ × (ℝ × ℝ) => (1 : ℝ))
          (volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R)) := integrable_const 1
      refine Integrable.mono' (hone.add (hbsq i))
        ((H.2.2.2.1.measurable i).norm.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
      show ‖‖b p i‖‖ ≤ 1 + ‖b p i‖ ^ 2
      rw [norm_norm]
      nlinarith [sq_nonneg (‖b p i‖ - 1 / 2)]
    -- the components of `f` are `L¹` on the band box (the sixth clause of `VtvHyps`)
    have hfi : ∀ i : Fin 2, Integrable (fun p : ℝ × (ℝ × ℝ) => ‖f p i‖)
        (volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R)) := by
      intro i
      have hm : MemLp (fun p : ℝ × (ℝ × ℝ) => f p i) 2
          (volume.restrict (Icc s₁ s₂ ×ˢ vtvBox c R)) :=
        (hf i).mono_measure
          (Measure.restrict_mono (Set.prod_mono subset_rfl (vtvBox_subset_cell c R)) le_rfl)
      exact (hm.integrable (by norm_num)).norm
    have hprodB : Integrable (fun p : ℝ × (ℝ × ℝ) => ‖b p 0‖ + ‖b p 1‖)
        ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (vtvBox c R))) := by
      rw [hprod]
      exact (hbi 0).add (hbi 1)
    have hprodF : Integrable (fun p : ℝ × (ℝ × ℝ) => ‖f p 0‖ + ‖f p 1‖)
        ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (vtvBox c R))) := by
      rw [hprod]
      exact (hfi 0).add (hfi 1)
    show Integrable (fun s => vtvDB c R b s + vtvDF c R f s) (volume.restrict (Icc s₁ s₂))
    exact hprodB.integral_prod_left.add hprodF.integral_prod_left
  · have hle : s₂ ≤ s₁ := not_lt.1 hlt
    have h0 : volume (Icc s₁ s₂) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.2 (by linarith)
    rw [IntegrableOn, Measure.restrict_eq_zero.2 h0]
    exact integrable_zero_measure

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
