import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_b

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/1`: `RelInteractionDysonJ` from its two halves

Source of record: `the November 2 reference manuscript` (SP), lines 2920-2925 and
2974-2978.  `relInteractionDysonJ` assembles `relInteractionA` (bounded damped complement
interaction, `org/1/a`) and `dysonDefined_of_measurable` (Dyson iterates defined under joint
measurability, `org/1/b`) with the clamped data `clampF B F_rel`, `clampA B A_rel`.

The only extra work is the measurability of `r ↦ A_rel (clampB B r) x` on all of `ℝ`: the
measurability of `A_rel · x` is given on `Icc 0 B` only, and the clamp is constant on each of
`Iio 0` and `Ioi B`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit

theorem clampB_eq_of_le_zero (B r : ℝ) (hr : r ≤ 0) : clampB B r = 0 :=
  max_eq_left (le_trans (min_le_left _ _) hr)

theorem clampB_eq_self_of_mem (B r : ℝ) (hr : r ∈ Icc 0 B) : clampB B r = r := by
  unfold clampB
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem clampB_eq_of_gt (B r : ℝ) (hB : 0 ≤ B) (hr : B < r) : clampB B r = B := by
  unfold clampB
  rw [min_eq_right hr.le, max_eq_right hB]

/-- Measurability of a clamped composition: if `g` is a.e. strongly measurable on `Icc 0 B`,
then `r ↦ g (clampB B r)` is a.e. strongly measurable on `ℝ`. -/
theorem aesm_comp_clampB {H : Type*} [NormedAddCommGroup H] (B : ℝ) (hB : 0 ≤ B) (g : ℝ → H)
    (hg : AEStronglyMeasurable g (volume.restrict (Icc 0 B))) :
    AEStronglyMeasurable (fun r => g (clampB B r)) volume := by
  have huniv : (Iio 0 ∪ Icc 0 B) ∪ Ioi B = univ := by
    ext x
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases h0 : x < 0
    · exact Or.inl (Or.inl h0)
    by_cases hB' : B < x
    · exact Or.inr hB'
    exact Or.inl (Or.inr ⟨not_lt.mp h0, not_lt.mp hB'⟩)
  have hsplit : (volume : Measure ℝ) = volume.restrict ((Iio 0 ∪ Icc 0 B) ∪ Ioi B) := by
    rw [huniv, Measure.restrict_univ]
  rw [hsplit, aestronglyMeasurable_union_iff, aestronglyMeasurable_union_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine (aestronglyMeasurable_const (b := g 0)).congr ?_
    have h : ∀ r ∈ Iio (0 : ℝ), g 0 = g (clampB B r) := fun r hr => by
      rw [clampB_eq_of_le_zero B r (le_of_lt hr)]
    exact ae_restrict_of_forall_mem measurableSet_Iio h
  · refine hg.congr ?_
    have h : ∀ r ∈ Icc (0 : ℝ) B, g r = g (clampB B r) := fun r hr => by
      rw [clampB_eq_self_of_mem B r hr]
    exact ae_restrict_of_forall_mem measurableSet_Icc h
  · refine (aestronglyMeasurable_const (b := g B)).congr ?_
    have h : ∀ r ∈ Ioi B, g B = g (clampB B r) := fun r hr => by
      rw [clampB_eq_of_gt B r hB hr]
    exact ae_restrict_of_forall_mem measurableSet_Ioi h

/-- **Leaf `org/1`** (SP 2920-2925, 2974-2978): the joint-measurability form of the
damped complement interaction and Dyson iteration, assembled from `relInteractionA` and
`dysonDefined_of_measurable`. -/
theorem relInteractionDysonJ (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelInteractionDysonJ κ := by
  unfold RelInteractionDysonJ
  intro hκ P hP m hm K B M_free b_free hB hM hb
  obtain ⟨K_A, b', hKA, hb'⟩ := relInteractionA κ hκ P hP m hm K B hB
  refine ⟨K_A, max b_free b', hKA, le_max_left _ _, fun b hbge => ?_⟩
  obtain ⟨ν_prop, hνp, hνprop⟩ := hb' b (le_trans (le_max_right _ _) hbge)
  refine ⟨ν_prop, hνp, fun ν hν hF tr htr t₁ t₂ ht₁ ht₁₂ hbt hBt F_rel hFrel hFbd hFmeas hFj => ?_⟩
  obtain ⟨A_rel, hA_int, hA_bd, hA_meas⟩ :=
    hνprop ν hν hF tr htr t₁ t₂ ht₁ ht₁₂ hbt hBt
  refine ⟨A_rel, hA_int, hA_bd, ?_⟩
  have hF' : ∀ s t : ℝ, s ≤ t → t ≤ s + B → ‖clampF B F_rel t s‖ ≤ M_free := by
    intro s t hst htB
    have h1 := clampB_mono B hst
    have h2 := clampB_le B t hB.le
    have h3 := clampB_nonneg B s
    exact hFbd (clampB B s) (clampB B t) h1 (by linarith)
  have hA' : ∀ r : ℝ, ‖clampA B A_rel r‖ ≤ K_A := fun r => hA_bd (clampB B r)
  have hFm' : ∀ (t : ℝ) (x : Planar.L2w m),
      AEStronglyMeasurable (fun σ => clampF B F_rel t σ x) volume := by
    intro t x
    exact ((hFj x).comp_measurable
      (measurable_const.prodMk measurable_id : Measurable fun σ : ℝ => (t, σ))).aestronglyMeasurable
  have hAm' : ∀ x : Planar.L2w m, AEStronglyMeasurable (fun r => clampA B A_rel r x) volume := by
    intro x
    exact aesm_comp_clampB B hB.le (fun τ => A_rel τ x) (hA_meas x)
  haveI hsepL : TopologicalSpace.SeparableSpace (Planar.L2w m) := by
    haveI : SFinite (UnforcedLeray.Planar.wMeasure m) := by
      unfold UnforcedLeray.Planar.wMeasure
      infer_instance
    haveI : MeasureTheory.IsSeparable (UnforcedLeray.Planar.wMeasure m) := inferInstance
    haveI : SecondCountableTopology (Planar.L2w m) := MeasureTheory.Lp.SecondCountableTopology
    exact inferInstance
  exact UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.dysonDefined_of_measurable
    B M_free K_A (clampF B F_rel) (clampA B A_rel) hF' hA' hFm' hFj hAm'

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit
