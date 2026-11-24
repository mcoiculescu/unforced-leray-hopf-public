import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_1
import UnforcedLeray.Lib.Cylinder.Basic

/-!

Source: `the November 2 reference manuscript` lines 1933-1935.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Function
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cyl

/-- A periodic function that is a.e. strongly measurable on one centred cell is a.e. strongly
measurable on the plane. -/
theorem ppl_aesm_of_cell {E : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] {c : ℝ} (hc : 0 < c)
    {f : ℝ × ℝ → E} (hf : IsPeriodic c f)
    (hm : AEStronglyMeasurable f (volume.restrict (cell c))) :
    AEStronglyMeasurable f volume := by
  have key : ∀ (n : ℤ) (x : ℝ × ℝ), f (x - n • ((c, 0) : ℝ × ℝ)) = f x := by
    intro n x
    have h := hf.add_zsmul (-n) x
    have e : x - n • ((c, 0) : ℝ × ℝ) = (x.1 + (-n) • c, x.2) := by
      ext <;> simp [sub_eq_add_neg, neg_smul]
    rw [e]
    exact h
  have hcover : (⋃ n : ℤ, (fun x : ℝ × ℝ => x - n • ((c, 0) : ℝ × ℝ)) ⁻¹' cell c) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨m, hm', -⟩ := existsUnique_add_zsmul_mem_Ico hc x.1 (-c / 2)
    refine ⟨-m, ?_⟩
    show x - (-m) • ((c, 0) : ℝ × ℝ) ∈ cell c
    rw [mem_cell]
    simp only [Prod.smul_fst, Prod.fst_sub]
    rw [neg_smul, sub_neg_eq_add]
    have hm2 : -c / 2 ≤ x.1 + m • c ∧ x.1 + m • c < -c / 2 + c := hm'
    constructor
    · linarith [hm2.1]
    · have := hm2.2
      have e2 : -c / 2 + c = c / 2 := by ring
      linarith [hm2.2, e2]
  rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ × ℝ))), ← hcover,
    aestronglyMeasurable_iUnion_iff]
  intro n
  have hmp : MeasurePreserving (fun x : ℝ × ℝ => x - n • ((c, 0) : ℝ × ℝ))
      (volume.restrict ((fun x : ℝ × ℝ => x - n • ((c, 0) : ℝ × ℝ)) ⁻¹' cell c))
      (volume.restrict (cell c)) :=
    (measurePreserving_sub_right volume (n • ((c, 0) : ℝ × ℝ))).restrict_preimage
      (measurableSet_cell c)
  exact (hm.comp_measurePreserving hmp).congr (Eventually.of_forall fun x => key n x)

/-- Each period strip `[a, a + n c) × ℝ` carries `n` cells of a periodic density. -/
theorem ppl_lintegral_strip {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℝ≥0∞} (hf : IsPeriodic c f)
    (a : ℝ) (n : ℕ) :
    ∫⁻ z in Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ), f z = (n : ℝ≥0∞) * ∫⁻ z in cell c, f z := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ (n : ℝ) * c := by positivity
    have h1 : a ≤ a + (n : ℝ) * c := by linarith
    have h2 : a + (n : ℝ) * c ≤ a + (n : ℝ) * c + c := by linarith
    have e : a + ((n + 1 : ℕ) : ℝ) * c = a + (n : ℝ) * c + c := by push_cast; ring
    have hB : MeasurableSet (Ico (a + (n : ℝ) * c) (a + (n : ℝ) * c + c) ×ˢ (univ : Set ℝ)) :=
      measurableSet_Ico.prod MeasurableSet.univ
    have hD : Disjoint (Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ))
        (Ico (a + (n : ℝ) * c) (a + (n : ℝ) * c + c) ×ˢ (univ : Set ℝ)) := by
      rw [Set.disjoint_prod]
      exact Or.inl Set.Ico_disjoint_Ico_same
    rw [e, ← Set.Ico_union_Ico_eq_Ico h1 h2, Set.union_prod, lintegral_union hB hD, ih a,
      lintegral_strip_eq_cell hc hf (a + (n : ℝ) * c)]
    push_cast
    ring

/-- **Task `PartII-b:T12/1/4/1/1`** (`PPLCutNorm`). -/
theorem ppl_cut_norm : UnforcedLeray.Short.IIb.PPLCutNorm := by
  intro c hc p hp F hF N
  obtain ⟨hper, hLp⟩ := hF
  have hperF : IsPeriodic c F := hper
  -- measurability of `F` on the plane
  have hmeasF : AEStronglyMeasurable F volume := by
    apply ppl_aesm_of_cell hc hperF
    have hk : ENNReal.ofReal c • avgμ c = volume.restrict (cell c) := by
      rw [avgμ, smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
        one_smul]; rfl
    have := hLp.aestronglyMeasurable.smul_measure (ENNReal.ofReal c)
    rwa [hk] at this
  have hSeq : {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 < (N : ℝ) * c} = Ico 0 ((N : ℝ) * c) ×ˢ (univ : Set ℝ) := by
    ext z
    simp
  have hSmeas : MeasurableSet (Ico 0 ((N : ℝ) * c) ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hcut : ppCut c N F = (Ico 0 ((N : ℝ) * c) ×ˢ (univ : Set ℝ)).indicator F := by
    unfold ppCut
    rw [hSeq]
  -- the lintegral identities
  have hfp : IsPeriodic c (fun z : ℝ × ℝ => ‖F z‖ₑ ^ p) := by
    intro z
    simp only [hperF z]
  have hstrip := ppl_lintegral_strip hc hfp 0 N
  rw [zero_add] at hstrip
  have hcell : ∫⁻ z, ‖F z‖ₑ ^ p ∂avgμ c = ENNReal.ofReal c⁻¹ * ∫⁻ z in cell c, ‖F z‖ₑ ^ p :=
    lintegral_avgμ _
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hLpE : eLpNorm F (ENNReal.ofReal p) (avgμ c) =
      (ENNReal.ofReal c⁻¹ * ∫⁻ z in cell c, ‖F z‖ₑ ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt, hpr, hcell]
  have hcutE : eLpNorm (ppCut c N F) (ENNReal.ofReal p) volume =
      ((N : ℝ≥0∞) * ∫⁻ z in cell c, ‖F z‖ₑ ^ p) ^ (1 / p) := by
    rw [hcut, eLpNorm_indicator_eq_eLpNorm_restrict hSmeas,
      eLpNorm_eq_lintegral_rpow_enorm hp0 hpt, hpr, ← hstrip]
  have hScale : ENNReal.ofReal ((N : ℝ) * c) * ENNReal.ofReal c⁻¹ = (N : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : (N : ℝ) * c * c⁻¹ = N := by field_simp
    rw [this, ENNReal.ofReal_natCast]
  have hEq : eLpNorm (ppCut c N F) (ENNReal.ofReal p) volume =
      ENNReal.ofReal ((N : ℝ) * c) ^ (1 / p) * eLpNorm F (ENNReal.ofReal p) (avgμ c) := by
    rw [hcutE, hLpE, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p),
      ← mul_assoc, hScale]
  have hfin : eLpNorm (ppCut c N F) (ENNReal.ofReal p) volume < ⊤ := by
    rw [hEq]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      hLp.eLpNorm_lt_top
  refine ⟨⟨?_, hfin⟩, hEq⟩
  rw [hcut]
  exact hmeasF.indicator hSmeas

#print axioms UnforcedLeray.Short.IIb.ppl_cut_norm
