import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Congr
import UnforcedLeray.Units.B0225

/-!
# `PartII-a:N01/9/1/2/3`: `r0Entrance`

Source `shorter-proof-2026-11-02.tex` 1684-1689, 3426-3430.  `R₀(μ)g ∈ 𝓗 = L²(measureH)` and the
recentred chart `Chart ∋ x ↦ cellPtInv c x` carries `ageμ c (-3/2)` (`c⁻¹ s^{-3/2} ds dq dη` on
`(0,∞) × [-c/2,c/2) × ℝ`) onto at most two copies of the cell with `measureH`'s density; hence the
chart energy is at most `2 c⁻¹ ‖R₀ g‖²_𝓗 < ∞` (we take `δ = 1` and drop the restriction).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH weightH cell)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv)

/-- Pointwise: `vnorm2 (velF c f x)^2` is the squared norm of `f` at the recentred point. -/
theorem ofReal_vnorm2_sq (c : ℝ) (f : Profile → MeridC) (x : ℝ × (ℝ × ℝ)) :
    ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2
      (UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c f x) ^ 2) =
      ‖f (cellPtInv c x)‖ₑ ^ (2 : ℝ) := by
  unfold UnforcedLeray.Short.IIIa.vnorm2 UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
    EuclideanSpace.norm_sq_eq]

theorem measurable_translate (c : ℝ) :
    MeasurePreserving (fun x : ℝ × (ℝ × ℝ) => (x.1, (x.2.1 + c, x.2.2))) volume volume := by
  have : (volume : Measure (ℝ × (ℝ × ℝ))).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have key : (fun x : ℝ × (ℝ × ℝ) => (x.1, (x.2.1 + c, x.2.2))) =
      fun x => x + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) := by
    funext x
    exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  rw [key]
  exact measurePreserving_add_right volume _

/-- Two copies of the cell dominate the recentred strip. -/
theorem strip_le_two_cell {c : ℝ} (hc : 0 < c) {Φ : Profile → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x in Ioi (0 : ℝ) ×ˢ qCell c, Φ (cellPtInv c x) ≤ 2 * ∫⁻ p in cell c, Φ p := by
  have hmS1 : MeasurableSet {x : ℝ × (ℝ × ℝ) | x ∈ Ioi (0 : ℝ) ×ˢ qCell c ∧ 0 < x.2.1} :=
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)).inter
      (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))
  have hmS2 : MeasurableSet {x : ℝ × (ℝ × ℝ) | x ∈ Ioi (0 : ℝ) ×ˢ qCell c ∧ ¬ 0 < x.2.1} :=
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)).inter
      (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).compl
  have hsplit : Ioi (0 : ℝ) ×ˢ qCell c ⊆
      {x : ℝ × (ℝ × ℝ) | x ∈ Ioi (0 : ℝ) ×ˢ qCell c ∧ 0 < x.2.1} ∪
      {x : ℝ × (ℝ × ℝ) | x ∈ Ioi (0 : ℝ) ×ˢ qCell c ∧ ¬ 0 < x.2.1} := by
    intro x hx
    by_cases h : 0 < x.2.1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hΦc : Measurable fun x => Φ (cellPtInv c x) :=
    hΦ.comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPtInv c)
  refine (lintegral_mono_set hsplit).trans ((lintegral_union_le _ _ _).trans ?_)
  have h1 : ∫⁻ x in {x : ℝ × (ℝ × ℝ) | x ∈ Ioi (0 : ℝ) ×ˢ qCell c ∧ 0 < x.2.1},
      Φ (cellPtInv c x) ≤ ∫⁻ p in cell c, Φ p := by
    rw [setLIntegral_congr_fun hmS1 (g := fun x => Φ x) (fun x hx => by
      unfold cellPtInv; rw [if_pos hx.2])]
    refine lintegral_mono_set ?_
    intro x hx
    obtain ⟨⟨hs, hq, -⟩, h0⟩ := hx
    exact ⟨hs, ⟨h0, by have := hq.2; unfold qCell at *; linarith⟩, trivial⟩
  have h2 : ∫⁻ x in {x : ℝ × (ℝ × ℝ) | x ∈ Ioi (0 : ℝ) ×ˢ qCell c ∧ ¬ 0 < x.2.1},
      Φ (cellPtInv c x) ≤ ∫⁻ p in cell c, Φ p := by
    have hT := measurable_translate c
    have hcellm : MeasurableSet (cell c) :=
      measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
    rw [setLIntegral_congr_fun hmS2
      (g := fun x => Φ ((fun x : ℝ × (ℝ × ℝ) => (x.1, (x.2.1 + c, x.2.2))) x))
      (fun x hx => by unfold cellPtInv; rw [if_neg hx.2])]
    refine le_trans (lintegral_mono_set ?_) (hT.setLIntegral_comp_preimage hcellm hΦ).le
    intro x hx
    obtain ⟨⟨hs, hq, -⟩, h0⟩ := hx
    obtain ⟨hq1, hq2⟩ := hq
    exact ⟨hs, ⟨by linarith, by push_neg at h0; linarith⟩, trivial⟩
  calc _ ≤ (∫⁻ p in cell c, Φ p) + ∫⁻ p in cell c, Φ p := add_le_add h1 h2
    _ = 2 * ∫⁻ p in cell c, Φ p := by rw [two_mul]

theorem r0Entrance : UnforcedLeray.Short.PartIIa.N01.R0Entrance := by
  intro c ν hc hν μ hμ g
  refine ⟨1, one_pos, ?_⟩
  set f : HSpace c MeridC := UnforcedLeray.B0225.R0 hc ν μ g with hf
  have hfm : Measurable (f : Profile → MeridC) := (Lp.stronglyMeasurable f).measurable
  have hfin0 : ∫⁻ p, ‖(f : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂measureH c < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
      (Lp.memLp f).eLpNorm_lt_top (f := (f : Profile → MeridC)) (μ := measureH c)
    simpa using this
  generalize (f : Profile → MeridC) = F at hfm hfin0 ⊢
  have hE : Measurable fun p : Profile => ‖F p‖ₑ ^ (2 : ℝ) := hfm.enorm.pow_const _
  have hΦ : Measurable fun p : Profile => weightH p * ‖F p‖ₑ ^ (2 : ℝ) :=
    UnforcedLeray.B0220.measurable_weightH.mul hE
  have hcell : ∫⁻ p in cell c, weightH p * ‖F p‖ₑ ^ (2 : ℝ) =
      ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂measureH c := by
    unfold measureH UnforcedLeray.B0220.cellMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH hE]
    rfl
  refine lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) ?_
  have hG : Measurable fun x : ℝ × (ℝ × ℝ) => ‖F (cellPtInv c x)‖ₑ ^ (2 : ℝ) :=
    hE.comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPtInv c)
  simp_rw [ofReal_vnorm2_sq]
  rw [lintegral_ageμ hc _ hG]
  have hmS : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpt : ∀ x ∈ Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * x.1 ^ (-3 / 2 : ℝ)) * ‖F (cellPtInv c x)‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal c⁻¹ * (weightH (cellPtInv c x) * ‖F (cellPtInv c x)‖ₑ ^ (2 : ℝ)) := by
    intro x hx
    have hw : ENNReal.ofReal (x.1 ^ (-3 / 2 : ℝ)) = weightH (cellPtInv c x) := by
      unfold weightH cellPtInv
      simp [neg_div]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), mul_assoc, hw]
  rw [setLIntegral_congr_fun hmS hpt, lintegral_const_mul
      (f := fun x => weightH (cellPtInv c x) * ‖F (cellPtInv c x)‖ₑ ^ (2 : ℝ)) _ (hΦ.comp
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPtInv c))]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine lt_of_le_of_lt (strip_le_two_cell hc hΦ) ?_
  rw [hcell]
  exact ENNReal.mul_lt_top (by norm_num) hfin0

end UnforcedLeray.Short.PartIIa.N01
