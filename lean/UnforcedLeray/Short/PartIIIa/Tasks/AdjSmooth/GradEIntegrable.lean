import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GradEAux

/-- For `f ∈ L²`, the real energy `∫‖f‖²` has the lower-integral `∫⁻‖f‖ₑ^2` as its `ofReal`. -/
lemma ofReal_integral_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℂ}
    (hf : MemLp f 2 μ) :
    ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.norm.integrable_sq
    (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

end GradEAux

theorem gradEIntegrable : UnforcedLeray.Short.IIIa.GradEIntegrable := by
  intro c m t s ψ hc hts hj hm hfin r hr
  obtain ⟨μ, hμ⟩ : ∃ μ, B0579.cellMeasure c (-m) = μ := ⟨_, rfl⟩
  rw [hμ] at hm hfin
  have hSF : SFinite μ := by
    rw [← hμ]
    unfold B0579.cellMeasure
    infer_instance
  have hrt : t ≤ r := hr.1
  have hrs : r < s := hr.2
  have hgnn : ∀ ρ, 0 ≤ gradE c m (ψ ρ) := fun ρ => by
    unfold gradE
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => by positivity
  -- the k-th slice energy as a measurable function of the age
  have hcont : ∀ k : Fin 2,
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (ψ p.1) p.2) (Ico t s ×ˢ univ) :=
    fun k => (jointSmooth_pdCx hj k).continuousOn
  have hmeasG : ∀ k : Fin 2, AEStronglyMeasurable
      (fun ρ => ∫ x, ‖pdCx k (ψ ρ) x‖ ^ 2 ∂μ) (volume.restrict (Ioc t r)) := by
    intro k
    obtain ⟨F, hF⟩ : ∃ F : ℝ × (ℝ × ℝ) → ℂ, F = (Ico t s ×ˢ (univ : Set (ℝ × ℝ))).piecewise
        (fun p => pdCx k (ψ p.1) p.2) (fun _ => 0) := ⟨_, rfl⟩
    have hFm : Measurable F := by
      rw [hF]
      exact ContinuousOn.measurable_piecewise (hcont k) continuousOn_const
        (measurableSet_Ico.prod MeasurableSet.univ)
    have hsm : StronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => ‖F p‖ ^ 2) :=
      ((hFm.norm.pow_const 2)).stronglyMeasurable
    have hint := hsm.integral_prod_right' (ν := μ)
    refine hint.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    have hρ' : ρ ∈ Ico t s := ⟨hρ.1.le, hρ.2.trans_lt hrs⟩
    congr 1
    funext x
    have hmem : (ρ, x) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hρ', mem_univ x⟩
    rw [hF, Set.piecewise_eq_of_mem _ _ _ hmem]
  -- the lower integrals of the slice energies
  have hAEφ : ∀ k : Fin 2, AEMeasurable (fun ρ => ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂μ)
      (volume.restrict (Ioc t r)) := by
    intro k
    refine AEMeasurable.congr (hmeasG k).aemeasurable.ennreal_ofReal ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    have hρ' : ρ ∈ Ico t s := ⟨hρ.1.le, hρ.2.trans_lt hrs⟩
    exact GradEAux.ofReal_integral_sq_eq μ (hm ρ hρ' k)
  have hpt : ∀ ρ ∈ Ioc t r, ENNReal.ofReal (gradE c m (ψ ρ)) =
      ∑ k, ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂μ := by
    intro ρ hρ
    have hρ' : ρ ∈ Ico t s := ⟨hρ.1.le, hρ.2.trans_lt hrs⟩
    have e : gradE c m (ψ ρ) = ∑ k, ∫ x, ‖pdCx k (ψ ρ) x‖ ^ 2 ∂μ := by
      unfold gradE
      rw [hμ]
    rw [e, ENNReal.ofReal_sum_of_nonneg (fun k _ => integral_nonneg fun x => by positivity)]
    exact Finset.sum_congr rfl fun k _ => GradEAux.ofReal_integral_sq_eq μ (hm ρ hρ' k)
  -- finiteness of the sum of slice energies on `(t, r]`
  have hint_fin : ∫⁻ ρ in Ioc t r, ∑ k, ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
    rw [lintegral_finsetSum' Finset.univ (fun k _ => hAEφ k)]
    refine ENNReal.sum_lt_top.2 fun k _ => ?_
    calc ∫⁻ ρ in Ioc t r, ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ∫⁻ ρ in Ioc t s, ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_mono_set (Ioc_subset_Ioc_right hrs.le)
      _ < ⊤ := hfin k
  have hfinite : HasFiniteIntegral (fun ρ => gradE c m (ψ ρ)) (volume.restrict (Ioc t r)) := by
    unfold HasFiniteIntegral
    have heq : ∫⁻ ρ in Ioc t r, ‖gradE c m (ψ ρ)‖ₑ =
        ∫⁻ ρ in Ioc t r, ∑ k, ∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
      rw [Real.enorm_eq_ofReal (hgnn ρ), hpt ρ hρ]
    rw [heq]
    exact hint_fin
  have hmeas : AEStronglyMeasurable (fun ρ => gradE c m (ψ ρ)) (volume.restrict (Ioc t r)) := by
    have e : (fun ρ => gradE c m (ψ ρ)) = fun ρ => ∑ k, ∫ x, ‖pdCx k (ψ ρ) x‖ ^ 2 ∂μ := by
      funext ρ
      unfold gradE
      rw [hμ]
    rw [e]
    exact Finset.aestronglyMeasurable_sum Finset.univ fun k _ => hmeasG k
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrt]
  exact ⟨hmeas, hfinite⟩

end UnforcedLeray.Short.IIIa
