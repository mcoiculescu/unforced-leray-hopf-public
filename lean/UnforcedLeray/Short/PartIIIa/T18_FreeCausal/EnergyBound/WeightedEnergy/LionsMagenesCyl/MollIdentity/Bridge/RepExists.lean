import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2.Bridge_Sub
import UnforcedLeray.Lib.BochnerTime.Slices

/-!
# `lmRepExists`: measurable `L²(cell; ℝ⁴)`-valued representatives

The slice path `s ↦ (x ↦ lmReal (u s x))` of a jointly measurable field is an `LMH c`-valued
path, by `BochnerTime.toPathLq` (`Lib/BochnerTime/Slices.lean`). Its strong measurability holds
for any strongly measurable field (`stronglyMeasurable_toPathLq`); local `L²` bounds give
Bochner integrability on `Ioo a b` (`stronglyMeasurable_toPath_Lq`), and a.e. membership of the
slices in `L²(cell)` gives the representation `LMRep`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open UnforcedLeray.BochnerTime
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

instance lmFact_one_le_two : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
instance lmFact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

lemma lmReal_continuous : Continuous lmReal := by
  unfold lmReal
  fun_prop

lemma vnorm2_continuous : Continuous vnorm2 := by
  unfold vnorm2
  exact Continuous.sqrt (continuous_finsetSum _ fun i _ => ((continuous_apply i).norm).pow 2)

lemma norm_lmReal_sq (z : Fin 2 → ℂ) : ‖lmReal z‖ ^ 2 = vnorm2 z ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (by positivity), EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [lmReal, Fin.sum_univ_four, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply,
    Real.norm_eq_abs, sq_abs]
  ring

lemma enorm_lmReal_sq (z : Fin 2 → ℂ) :
    ‖lmReal z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (vnorm2 z ^ 2) := by
  rw [← ofReal_norm (lmReal z), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, norm_lmReal_sq]

/-- The real representation of a field, as a function of space-time. -/
def lmF (u : ℝ → LMSpField) : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 4) :=
  fun p => lmReal (u p.1 p.2)

/-- The `LMH c`-valued slice path of `u`. -/
def lmPath (c : ℝ) (u : ℝ → LMSpField) : ℝ → LMH c :=
  toPathLq 2 (volume.restrict (B0579.cell c)) (lmF u)

lemma lmF_measurable (u : ℝ → LMSpField)
    (hu : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i) :
    Measurable (lmF u) := by
  have hv : Measurable fun p : ℝ × (ℝ × ℝ) => (fun i => u p.1 p.2 i) := measurable_pi_iff.2 hu
  exact lmReal_continuous.measurable.comp hv

lemma memLp_two_of_lintegral_lt {E : Type*} [NormedAddCommGroup E] {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {g : α → E} (hm : AEStronglyMeasurable g μ)
    (h : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ < ⊤) : MemLp g 2 μ := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simpa using h

lemma ae_slice_lt_top (g : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) (I : Set ℝ)
    (C : Set (ℝ × ℝ)) (h : ∫⁻ p in I ×ˢ C, g p < ⊤) :
    ∀ᵐ s ∂(volume.restrict I), ∫⁻ x in C, g (s, x) < ⊤ := by
  have e : ∫⁻ p in I ×ˢ C, g p = ∫⁻ s in I, ∫⁻ x in C, g (s, x) := by
    rw [show (volume : Measure (ℝ × (ℝ × ℝ))) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))
      from rfl, ← Measure.prod_restrict]
    exact lintegral_prod _ hg.aemeasurable
  rw [e] at h
  exact ae_lt_top hg.lintegral_prod_right' h.ne

lemma lmPath_memLp_Ioo (c : ℝ) (u : ℝ → LMSpField)
    (hu : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hl : ∫⁻ p in Icc a b ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤) :
    MemLp (lmPath c u) 2 (volume.restrict (Ioo a b)) := by
  show MemLp (toPathLq 2 (volume.restrict (B0579.cell c)) (lmF u)) 2 (volume.restrict (Ioo a b))
  have hF : MemLp (lmF u) 2
      ((volume.restrict (Ioo a b)).prod (volume.restrict (B0579.cell c))) := by
    apply memLp_two_of_lintegral_lt (lmF_measurable u hu).aestronglyMeasurable
    rw [Measure.prod_restrict]
    simp only [lmF, enorm_lmReal_sq]
    exact lt_of_le_of_lt (lintegral_mono_set (prod_mono Ioo_subset_Icc_self subset_rfl)) hl
  have h1 := (stronglyMeasurable_toPath_Lq hF).1
  have h2 := (stronglyMeasurable_toPath_Lq hF).2
  refine memLp_two_of_lintegral_lt h1 ?_
  simp only [ENNReal.toReal_ofNat] at h2
  rw [h2]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF.eLpNorm_lt_top.ne

lemma ae_Ioi_lt_top (c : ℝ) (u : ℝ → LMSpField)
    (hu : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    (hl : ∀ s1 s2 : ℝ, 0 < s1 → s1 < s2 →
      ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u s x i) ^ 2) < ⊤ := by
  have hv : Measurable fun p : ℝ × (ℝ × ℝ) => (fun i => u p.1 p.2 i) := measurable_pi_iff.2 hu
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((vnorm2_continuous.measurable.comp hv).pow_const 2)
  have key : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u s x i) ^ 2) < ⊤ := by
    intro n
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 1 / ((n : ℝ) + 1) < (n : ℝ) + 2 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact ae_slice_lt_top _ hg _ _ (hl _ _ h1 h2)
  have hcover : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / s) s)
    rw [mem_iUnion]
    refine ⟨n, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / s ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      rw [div_le_iff₀ hs'] at h1
      nlinarith
    · have : s ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      linarith
  have hall : ∀ᵐ s ∂(volume.restrict (⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u s x i) ^ 2) < ⊤ := by
    rw [ae_restrict_iUnion_iff]
    exact key
  exact ae_restrict_of_ae_restrict_of_subset hcover hall

lemma lmRep_of_local (c : ℝ) (u : ℝ → LMSpField)
    (hu : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    (hl : ∀ s1 s2 : ℝ, 0 < s1 → s1 < s2 →
      ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤) :
    LMRep c u (lmPath c u) := by
  filter_upwards [ae_Ioi_lt_top c u hu hl] with s hs
  have hmeas : Measurable fun x => lmF u (s, x) :=
    (lmF_measurable u hu).comp measurable_prodMk_left
  have hmem : MemLp (fun x => lmF u (s, x)) 2 (volume.restrict (B0579.cell c)) := by
    apply memLp_two_of_lintegral_lt hmeas.aestronglyMeasurable
    simp only [lmF, enorm_lmReal_sq]
    exact hs
  rw [show lmPath c u s = hmem.toLp _ from toPathLq_of_memLp hmem]
  exact hmem.coeFn_toLp

lemma lmRepExists_proof : LMRepExists := by
  intro c _ u u' hW
  refine ⟨lmPath c u, lmPath c u', lmRep_of_local c u hW.measU hW.l2U,
    lmRep_of_local c u' hW.measU' hW.l2U', fun a b ha hab => ⟨?_, ?_⟩⟩
  · exact (lmPath_memLp_Ioo c u hW.measU a b ha hab (hW.l2U a b ha hab)).integrable (by norm_num)
  · exact (lmPath_memLp_Ioo c u' hW.measU' a b ha hab (hW.l2U' a b ha hab)).integrable (by norm_num)

theorem lmRepExists : UnforcedLeray.Short.IIIa.LMRepExists := lmRepExists_proof

end UnforcedLeray.Short.IIIa
