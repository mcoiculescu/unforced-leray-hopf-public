import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart flowIntegrand trainVel flatDt flatLap lapP vnorm2 tnorm2)

private theorem slice_memLp_ae (F : ℝ × (ℝ × ℝ) → ℂ) (S : Set (ℝ × ℝ)) (a b : ℝ)
    (hF : MemLp F 2 (volume.restrict (Icc a b ×ˢ S))) :
    ∀ᵐ s ∂(volume.restrict (Icc a b)), MemLp (fun x => F (s, x)) 2 (volume.restrict S) := by
  have hv : (volume.restrict (Icc a b ×ˢ S) : Measure (ℝ × (ℝ × ℝ))) =
      (volume.restrict (Icc a b)).prod (volume.restrict S) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [hv] at hF
  have hint : Integrable (fun p => ‖F p‖ ^ 2) ((volume.restrict (Icc a b)).prod
      (volume.restrict S)) := (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  filter_upwards [hint.prod_right_ae, hF.1.prodMk_left] with s h1 h2
  exact (memLp_two_iff_integrable_sq_norm h2).2 h1

private theorem comp_memLp (c a b : ℝ) (ha : 0 < a) (hab : a < b) (B : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (hm : ∀ i, Measurable fun p => B p i)
    (hl : ∫⁻ p in Icc a b ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (B p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤) (i : Fin 2) :
    MemLp (fun p => B p i) 2 (volume.restrict (Icc a b ×ˢ B0579.cell c)) := by
  have hm' := (hm i).aestronglyMeasurable (μ := volume.restrict (Icc a b ×ˢ B0579.cell c))
  rw [memLp_two_iff_integrable_sq_norm hm']
  refine ⟨(hm'.norm.pow 2), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hl
  show ‖‖B p i‖ ^ 2‖ₑ ≤ _
  rw [Real.enorm_eq_ofReal (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖B p i‖ ^ 2 ≤ vnorm2 (B p) ^ 2 := by
    unfold vnorm2
    rw [Real.sq_sqrt (by positivity)]
    exact Finset.single_le_sum (f := fun j : Fin 2 => ‖B p j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have h2 : 0 ≤ tnorm2 (G p) ^ 2 := by positivity
  linarith

theorem sliceL2ae : SliceL2ae := by
  intro ν c μ tr ω g b G f H
  obtain ⟨hnu, hc, hBUC, hE, hBS, hf, hcurl, hid, hOmInt⟩ := H
  have key : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      SliceL2 c b f s := by
    intro n
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hab : 1 / ((n : ℝ) + 1) < (n : ℝ) + 2 := by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hb := fun i => slice_memLp_ae _ _ _ _
      (comp_memLp c _ _ ha hab b G hE.measurable (hE.energyLoc _ _ ha hab) i)
    have hf' := fun i => slice_memLp_ae _ _ _ _ (hf _ ((n : ℝ) + 2) ha i)
    have := (ae_all_iff.2 hb).and (ae_all_iff.2 hf')
    filter_upwards [this] with s hs i
    exact ⟨hs.1 i, hs.2 i⟩
  have key2 : ∀ᵐ s ∂(volume : Measure ℝ), ∀ n : ℕ,
      s ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) → SliceL2 c b f s := by
    rw [ae_all_iff]
    intro n
    exact (ae_restrict_iff' measurableSet_Icc).1 (key n)
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [key2] with s hs hpos
  have hpos' : (0 : ℝ) < s := hpos
  obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt hpos'
  obtain ⟨n2, hn2⟩ := exists_nat_gt s
  refine hs (max n1 n2) ⟨?_, ?_⟩
  · have h1 : (1 : ℝ) / (((max n1 n2 : ℕ) : ℝ) + 1) ≤ 1 / ((n1 : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (n1 : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
      linarith
    linarith
  · have : (n2 : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
