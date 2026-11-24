import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2.Bridge_Sub
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge.RepExists

/-!
# `lmRepPair`: norm and pairing of the representatives

For a.e. `s > 0` the representatives satisfy `‖U s‖² = ∫_cell |u s|²` and
`⟪U' s, U s⟫ = Re ⟨u' s, u s⟩_{L²(cell;ℂ²)}` (`L2.inner_def`, pointwise `lmReal` identities).
Integrability on `Ioo a b` follows from `Tonelli` on `l2U` (`integrable_toReal_of_lintegral_ne_top`)
and the Cauchy-Schwarz bound `|⟪U', U⟫| ≤ (‖U'‖² + ‖U‖²)/2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open UnforcedLeray.BochnerTime
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIIa

lemma lmReal_inner (w z : Fin 2 → ℂ) :
    ⟪lmReal w, lmReal z⟫ = (∑ i : Fin 2, starRingEnd ℂ (w i) * z i).re := by
  simp [lmReal, PiLp.inner_apply, Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

lemma sq_le_vnorm2_sq (z : Fin 2 → ℂ) (i : Fin 2) : ‖z i‖ ^ 2 ≤ vnorm2 z ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (by positivity)]
  exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

lemma memLp_comp_of_lintegral {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → Fin 2 → ℂ}
    (hm : ∀ i : Fin 2, Measurable fun x => f x i)
    (hF : ∫⁻ x, ENNReal.ofReal (vnorm2 (f x) ^ 2) ∂μ < ⊤) (i : Fin 2) :
    MemLp (fun x => f x i) 2 μ := by
  refine memLp_two_of_lintegral_lt (hm i).aestronglyMeasurable (lt_of_le_of_lt ?_ hF)
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ofReal_norm (f x i), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]
  exact ENNReal.ofReal_le_ofReal (sq_le_vnorm2_sq (f x) i)

lemma integrable_conj_mul_of_memLp {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => starRingEnd ℂ (f x) * g x) μ := by
  have h := hf.star.integrable_mul hg
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Pi.mul_apply]

lemma integrable_LMIp_integrand {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → Fin 2 → ℂ}
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) (hg : ∀ i, MemLp (fun x => g x i) 2 μ) :
    Integrable (fun x => ∑ i : Fin 2, starRingEnd ℂ (f x i) * g x i) μ :=
  integrable_finsetSum _ fun i _ => integrable_conj_mul_of_memLp (hf i) (hg i)

lemma lintegral_slice_eq (g : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) (I : Set ℝ)
    (C : Set (ℝ × ℝ)) :
    ∫⁻ p in I ×ˢ C, g p = ∫⁻ s in I, ∫⁻ x in C, g (s, x) := by
  rw [show (volume : Measure (ℝ × (ℝ × ℝ))) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))
    from rfl, ← Measure.prod_restrict]
  exact lintegral_prod _ hg.aemeasurable

/-- The `L¹(s)` function `s ↦ ∫_cell |u s|²` is integrable on `Ioo a b`. -/
lemma integrable_sqNorm_Ioo (c : ℝ) (u : ℝ → LMSpField)
    (hu : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    (a b : ℝ) (hab : a < b)
    (hl : ∫⁻ p in Icc a b ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤) :
    IntegrableOn (fun s => ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2) (Ioo a b) := by
  have hv : Measurable fun p : ℝ × (ℝ × ℝ) => (fun i => u p.1 p.2 i) := measurable_pi_iff.2 hu
  set F : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2)
    with hFdef
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp ((vnorm2_continuous.measurable.comp hv).pow_const 2)
  set G : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in B0579.cell c, F (s, x) with hGdef
  have hGm : Measurable G := hF.lintegral_prod_right'
  have hG : ∫⁻ s in Ioo a b, G s < ⊤ := by
    have e1 := lintegral_slice_eq F hF (Ioo a b) (B0579.cell c)
    have e2 : ∫⁻ p in Ioo a b ×ˢ B0579.cell c, F p ≤ ∫⁻ p in Icc a b ×ˢ B0579.cell c, F p :=
      lintegral_mono_set (prod_mono Ioo_subset_Icc_self subset_rfl)
    have e3 : ∫⁻ s in Ioo a b, G s = ∫⁻ p in Ioo a b ×ˢ B0579.cell c, F p := e1.symm
    rw [e3]
    exact lt_of_le_of_lt e2 hl
  refine (integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hG.ne).congr
    (Filter.Eventually.of_forall fun s => ?_)
  show (G s).toReal = ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2
  rw [hGdef]
  rw [← integral_toReal]
  · congr 1
    ext x
    rw [hFdef, ENNReal.toReal_ofReal (sq_nonneg _)]
  · exact (hF.comp measurable_prodMk_left).aemeasurable
  · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top

lemma lmRepPair_proof : LMRepPair := by
  intro c _ u u' hW U U' hU hU'
  unfold LMRep at hU hU'
  have hm := hW.measU
  have hm' := hW.measU'
  have hl := hW.l2U
  have hl' := hW.l2U'
  have hA : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u s x i) ^ 2) < ⊤ :=
    ae_Ioi_lt_top c u hm hl
  have hA' : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u' s x i) ^ 2) < ⊤ :=
    ae_Ioi_lt_top c u' hm' hl'
  have key : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (‖U s‖ ^ 2 = ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2) ∧
      (⟪U' s, U s⟫ = (LMIp c (u' s) (u s)).re) ∧
      (‖U' s‖ ^ 2 = ∫ x in B0579.cell c, vnorm2 (u' s x) ^ 2) ∧
      ((LMIp c (u' s) (u s)).re =
        ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (u' s x i) * u s x i).re) := by
    filter_upwards [hA, hA', hU, hU'] with s hs hs' hr hr'
    have hmem : ∀ i, MemLp (fun x => u s x i) 2 (volume.restrict (B0579.cell c)) := fun i =>
      memLp_comp_of_lintegral (fun i => (hm i).comp measurable_prodMk_left) hs i
    have hmem' : ∀ i, MemLp (fun x => u' s x i) 2 (volume.restrict (B0579.cell c)) := fun i =>
      memLp_comp_of_lintegral (fun i => (hm' i).comp measurable_prodMk_left) hs' i
    have h1 : ‖U s‖ ^ 2 = ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hr] with x hx
      rw [hx, real_inner_self_eq_norm_sq, norm_lmReal_sq]
    have h3 : ‖U' s‖ ^ 2 = ∫ x in B0579.cell c, vnorm2 (u' s x) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hr'] with x hx
      rw [hx, real_inner_self_eq_norm_sq, norm_lmReal_sq]
    have h4 : (LMIp c (u' s) (u s)).re =
        ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (u' s x i) * u s x i).re := by
      unfold LMIp
      exact (integral_re (integrable_LMIp_integrand hmem' hmem)).symm
    have h2 : ⟪U' s, U s⟫ = ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (u' s x i) * u s x i).re := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hr, hr'] with x hx hx'
      rw [hx, hx', lmReal_inner]
    exact ⟨h1, h2.trans h4.symm, h3, h4⟩
  refine ⟨key.mono fun s hs => ⟨hs.1, hs.2.1⟩, fun a b ha hab => ⟨?_, ?_⟩⟩
  · exact integrable_sqNorm_Ioo c u hm a b hab (hl a b ha hab)
  · have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
    have hk := ae_restrict_of_ae_restrict_of_subset hsub key
    have hf : Measurable fun p : ℝ × (ℝ × ℝ) =>
        (∑ i : Fin 2, starRingEnd ℂ (u' p.1 p.2 i) * u p.1 p.2 i).re := by
      apply Complex.measurable_re.comp
      apply Finset.measurable_sum
      intro i _
      exact (Complex.continuous_conj.measurable.comp (hm' i)).mul (hm i)
    have hmeas : AEStronglyMeasurable (fun s => (LMIp c (u' s) (u s)).re)
        (volume.restrict (Ioo a b)) := by
      have hB := (hf.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (B0579.cell c))).aestronglyMeasurable (μ := volume.restrict (Ioo a b))
      exact hB.congr (hk.mono fun s hs => hs.2.2.2.symm)
    refine Integrable.mono' (((integrable_sqNorm_Ioo c u' hm' a b hab (hl' a b ha hab)).add
      (integrable_sqNorm_Ioo c u hm a b hab (hl a b ha hab))).div_const 2) hmeas ?_
    filter_upwards [hk] with s hs
    obtain ⟨h1, h2, h3, _⟩ := hs
    rw [← h2, Real.norm_eq_abs]
    have hc := abs_real_inner_le_norm (U' s) (U s)
    simp only [Pi.add_apply]
    rw [← h1, ← h3]
    nlinarith [sq_nonneg (‖U' s‖ - ‖U s‖), hc]

theorem lmRepPair : UnforcedLeray.Short.IIIa.LMRepPair := lmRepPair_proof

end UnforcedLeray.Short.IIIa
