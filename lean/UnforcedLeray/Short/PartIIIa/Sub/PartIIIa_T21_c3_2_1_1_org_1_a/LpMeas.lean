import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: measurability of `L²`-valued maps

A map `G : α → L²(μ)` whose values are represented by a jointly measurable function
`F : α → β → ℂ` is strongly measurable: the distance to any fixed element is a measurable
function of the parameter (Tonelli), and in the separable space `L²(μ)` the preimage of an open
set is a countable union of preimages of rational balls around a countable dense set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric TopologicalSpace
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

/-- The distance from a jointly represented `L²`-valued map to a fixed element is measurable. -/
theorem measurable_dist_Lp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β} [SFinite μ] (F : α → β → ℂ) (hF : Measurable (Function.uncurry F))
    (G : α → Lp ℂ 2 μ) (hG : ∀ a, (G a : β → ℂ) =ᵐ[μ] F a) (s : Lp ℂ 2 μ) :
    Measurable (fun a => dist (G a) s) := by
  have hs : StronglyMeasurable (s : β → ℂ) := Lp.stronglyMeasurable s
  have key : ∀ a, dist (G a) s =
      ((∫⁻ x, ‖F a x - s x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))).toReal := by
    intro a
    rw [Lp.dist_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2]
    congr 2
    apply lintegral_congr_ae
    filter_upwards [hG a] with x hx
    simp only [Pi.sub_apply, hx]
  simp_rw [key]
  refine (Measurable.pow_const ?_ _).ennreal_toReal
  refine Measurable.lintegral_prod_right'
    (f := fun p : α × β => ‖F p.1 p.2 - s p.2‖ₑ ^ (2 : ℝ)) ?_
  exact ((hF.sub (hs.measurable.comp measurable_snd)).enorm).pow_const _

/-- A map into a separable metric space whose distance to every point is measurable is
measurable. -/
theorem measurable_of_measurable_dist {α E : Type*} [MeasurableSpace α] [MetricSpace E]
    [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] (G : α → E)
    (hG : ∀ s, Measurable (fun a => dist (G a) s)) : Measurable G := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable S := hSc.to_subtype
  refine measurable_of_isOpen fun U hU => ?_
  have hEq : G ⁻¹' U = ⋃ p : S × ℚ,
      {a | ball (p.1 : E) (p.2 : ℝ) ⊆ U ∧ dist (G a) p.1 < p.2} := by
    ext a
    simp only [mem_preimage, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro ha
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (G a) ha
      obtain ⟨s, hsS, hs⟩ := hSd.exists_dist_lt (G a) (half_pos hε)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hs
      refine ⟨(⟨s, hsS⟩, q), ?_, hq1⟩
      intro y hy
      apply hball
      rw [mem_ball] at hy ⊢
      have h1 : dist y (G a) ≤ dist y s + dist s (G a) := dist_triangle _ _ _
      have h2 : dist s (G a) = dist (G a) s := dist_comm _ _
      simp only at hy
      linarith
    · rintro ⟨p, hp, hlt⟩
      exact hp (by rw [mem_ball]; exact hlt)
  rw [hEq]
  refine MeasurableSet.iUnion fun p => ?_
  by_cases h : ball (p.1 : E) (p.2 : ℝ) ⊆ U
  · simp only [h, true_and]
    exact measurableSet_lt (hG _) measurable_const
  · simp only [h, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

/-- **Strong measurability of jointly represented `L²`-valued maps.** -/
theorem stronglyMeasurable_Lp_of_jointly {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β] {μ : Measure β} [SFinite μ]
    (F : α → β → ℂ) (hF : Measurable (Function.uncurry F))
    (G : α → Lp ℂ 2 μ) (hG : ∀ a, (G a : β → ℂ) =ᵐ[μ] F a) : StronglyMeasurable G := by
  letI : MeasurableSpace (Lp ℂ 2 μ) := borel _
  haveI : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩
  exact (measurable_of_measurable_dist G (measurable_dist_Lp F hF G hG)).stronglyMeasurable

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
