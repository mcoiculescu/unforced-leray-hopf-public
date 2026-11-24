import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUSliceZero` (item `PartIII-b:C/near/delta/9/1/9`)

If the energy `E(s) = ∫_cell |b(s)|²` vanishes for a.e. `s ∈ (0,T)`, then `b = 0` a.e. on
`(0,T) × cell` (and hence on `(0,∞) × cell` with `s < T`).  Source 3541-3545 (uniqueness by the
energy identity on `[δ_j, B]`).

Route: Tonelli on `(0,T) × cell` for the nonnegative `ofReal |b|²`.  The inner cell integrals are
finite for a.e. `s ∈ (0,T)` (`energyLoc` on the intervals `[T/(n+2), T]`, countable cover), so each
slice is integrable and `ofReal (∫ ·) = ∫⁻ ofReal`; the slice integrals vanish, so the total
lintegral is `0`, and the a.e. vanishing of `|b|²` on the product gives `b = 0` componentwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- Finiteness of the inner lintegral for a.e. age: for a measurable `h ≥ 0`-valued function on
`X × C` with finite total lintegral, a.e. `s ∈ X` the cell lintegral is finite. -/
theorem fu_ae_lintegral_lt_top (X : Set ℝ) (C : Set (ℝ × ℝ)) (hX : MeasurableSet X)
    (hC : MeasurableSet C) {h : ℝ × (ℝ × ℝ) → ENNReal} (hh : Measurable h)
    (hfin : ∫⁻ p in X ×ˢ C, h p < ⊤) :
    ∀ᵐ s ∂(volume.restrict X), ∫⁻ x in C, h (s, x) < ⊤ := by
  have hprod : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (X ×ˢ C) =
      (volume.restrict X).prod (volume.restrict C) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hprod] at hfin
  rw [lintegral_prod h (hh.aemeasurable (μ := (volume.restrict X).prod (volume.restrict C)))]
    at hfin
  have hmeas : Measurable fun s => ∫⁻ x in C, h (s, x) := hh.lintegral_prod_right'
  filter_upwards [ae_lt_top hmeas (ne_of_lt hfin)] with s hs
  exact hs

theorem fuSliceZero : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUSliceZero := by
  intro c ν μ F b G T hc hsol hE0
  by_cases hT : 0 < T
  swap
  · -- `(0,T)` is empty, so the implication is vacuous on `(0,∞) × cell`
    have hcellm : MeasurableSet (UnforcedLeray.B0579.cell c) :=
      UnforcedLeray.B0579.measurableSet_cell c
    have hIm : MeasurableSet (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) :=
      measurableSet_Ioi.prod hcellm
    rw [ae_restrict_iff' hIm]
    exact ae_of_all _ fun p hmem hpT => absurd (lt_trans (show (0 : ℝ) < p.1 from hmem.1) hpT) hT
  have hf : Measurable fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2 :=
    UnforcedLeray.Short.IIIa.measurable_vnorm2_sq hsol.measurable
  have hfe : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2) := hf.ennreal_ofReal
  have hcellm : MeasurableSet (UnforcedLeray.B0579.cell c) :=
    UnforcedLeray.B0579.measurableSet_cell c
  -- (1) finiteness of the inner lintegrals for a.e. `s ∈ (0,T)`
  have hfin_s : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ∫⁻ x in UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2) < ⊤ := by
    have hcover : Ioo (0 : ℝ) T ⊆ ⋃ n : ℕ, Icc (T / ((n : ℝ) + 2)) T := by
      intro s hs
      obtain ⟨n, hn⟩ := exists_nat_gt (T / s)
      refine Set.mem_iUnion.2 ⟨n, ?_, le_of_lt hs.2⟩
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [div_le_iff₀ hpos]
      have h1 : T < (n : ℝ) * s := (div_lt_iff₀ hs.1).1 hn
      nlinarith [hs.1]
    have hfam : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Icc (T / ((n : ℝ) + 2)) T)),
        ∫⁻ x in UnforcedLeray.B0579.cell c,
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2) < ⊤ := by
      intro n
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have ha : 0 < T / ((n : ℝ) + 2) := div_pos hT (by positivity)
      have hab : T / ((n : ℝ) + 2) < T := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hT.le hn0]
      have hfinL : ∫⁻ p in Icc (T / ((n : ℝ) + 2)) T ×ˢ UnforcedLeray.B0579.cell c,
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2) < ⊤ :=
        (lintegral_mono (fun p => ENNReal.ofReal_le_ofReal
          (le_add_of_nonneg_right (sq_nonneg _)))).trans_lt (hsol.energyLoc _ _ ha hab)
      exact fu_ae_lintegral_lt_top _ _ measurableSet_Icc hcellm hfe hfinL
    have hall := (ae_restrict_iUnion_iff (fun n : ℕ => Icc (T / ((n : ℝ) + 2)) T)
      (fun s => ∫⁻ x in UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2) < ⊤)).2 hfam
    exact ae_restrict_of_ae_restrict_of_subset hcover hall
  -- (2) the slices are integrable for a.e. `s ∈ (0,T)`
  have hint_s : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)),
      Integrable (fun x : ℝ × ℝ => UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2)
        (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    filter_upwards [hfin_s] with s hs
    have hm_s : Measurable fun x : ℝ × ℝ => UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2 :=
      hf.comp measurable_prodMk_left
    refine ⟨hm_s.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).2 hs
  -- (3) the inner lintegrals vanish for a.e. `s ∈ (0,T)`
  have hinner : (fun s : ℝ => ∫⁻ x in UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2))
      =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] fun _ => (0 : ENNReal) := by
    filter_upwards [hE0, hint_s] with s hs0 hsi
    have h0 : ∫ x in UnforcedLeray.B0579.cell c,
        UnforcedLeray.Short.IIIa.vnorm2 (b (s, x)) ^ 2 = 0 := hs0
    have key := ofReal_integral_eq_lintegral_ofReal hsi (ae_of_all _ fun x => sq_nonneg _)
    rw [h0, ENNReal.ofReal_zero] at key
    exact key.symm
  -- (4) the total lintegral over `(0,T) × cell` vanishes
  have hS : ∫⁻ p in Ioo (0 : ℝ) T ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2) = 0 := by
    have hprod : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioo (0 : ℝ) T ×ˢ UnforcedLeray.B0579.cell c) =
        (volume.restrict (Ioo (0 : ℝ) T)).prod (volume.restrict (UnforcedLeray.B0579.cell c)) := by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hprod, lintegral_prod _ (hfe.aemeasurable
      (μ := (volume.restrict (Ioo (0 : ℝ) T)).prod (volume.restrict (UnforcedLeray.B0579.cell c))))]
    rw [lintegral_congr_ae hinner]
    simp
  -- (5) `|b|² = 0` a.e. on `(0,T) × cell`
  have hSm : MeasurableSet (Ioo (0 : ℝ) T ×ˢ UnforcedLeray.B0579.cell c) :=
    measurableSet_Ioo.prod hcellm
  have hae : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) T ×ˢ UnforcedLeray.B0579.cell c)),
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2) = 0 :=
    (lintegral_eq_zero_iff hfe).1 hS
  have hz' : ∀ᵐ p ∂(volume : Measure (ℝ × (ℝ × ℝ))),
      p ∈ Ioo (0 : ℝ) T ×ˢ UnforcedLeray.B0579.cell c →
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2) = 0 :=
    (ae_restrict_iff' hSm).1 hae
  -- (6) transfer to `(0,∞) × cell` with `s < T`, and conclude `b = 0`
  have hIm : MeasurableSet (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) :=
    measurableSet_Ioi.prod hcellm
  rw [ae_restrict_iff' hIm]
  filter_upwards [hz'] with p hp hmem hpT
  have hpS : p ∈ Ioo (0 : ℝ) T ×ˢ UnforcedLeray.B0579.cell c := ⟨⟨hmem.1, hpT⟩, hmem.2⟩
  have h0 := hp hpS
  have h1 : UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 h0
  have h2 : UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  have hsq : UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2 = ∑ j : Fin 2, ‖b p j‖ ^ 2 := by
    unfold UnforcedLeray.Short.IIIa.vnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  intro i
  have hi : ‖b p i‖ ^ 2 ≤ ∑ j : Fin 2, ‖b p j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 2 => ‖b p j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h3 : ‖b p i‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
