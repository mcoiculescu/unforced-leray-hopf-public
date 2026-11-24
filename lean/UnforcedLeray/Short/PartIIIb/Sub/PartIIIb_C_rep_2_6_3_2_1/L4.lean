import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a

/-!
# `extIntKdIntegrable` (`PartIII-b:C/rep/2/6/3/2/1/4`)

Source `the November 2 reference manuscript` lines 3611-3621, 3631-3646.
The shifted integrand `extInt T Kd t y i` is the image under the measure-preserving map
`(s,z) ↦ (t-s, z)` of the indicator of `Ioi 0 × Space` applied to the `(h,z)`-integrand of
`Kd = G_μ - G_{μ+1}`; its integrability on `volume.prod volume` is the integrability of that
integrand on `(volume.restrict (Ioi 0)).prod volume`, which is `gkerIntegrable` (twice).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem extIntKdIntegrable : ExtIntKdIntegrable := by
  intro ν μ rOut P T hD y hy i t
  obtain ⟨hν, hμ, hr, hP, hT, hM⟩ := hD
  have hμ' : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have I1 := gkerIntegrable ν (μ : ℂ) hν hμ' rOut P hr hP T hT hM t y hy i
  have I2 := gkerIntegrable ν ((μ : ℂ) + 1) hν hμ1 rOut P hr hP T hT hM t y hy i
  set f : ℝ × Space → ℂ := fun p => ∑ j : Fin 3, ∑ k : Fin 3,
    Kd ν μ p.1 y p.2 i j k * ((T (t - p.1) p.2 j k : ℝ) : ℂ) with hf
  have hsub : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have h := I1.sub I2
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [hf, Kd, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hrest : (volume.restrict (Ioi (0 : ℝ))).prod volume =
      (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  set H : ℝ × Space → ℂ := (Ioi (0 : ℝ) ×ˢ (univ : Set Space)).indicator f with hH
  have hHint : Integrable H (volume.prod volume) := by
    rw [hH, integrable_indicator_iff (measurableSet_Ioi.prod MeasurableSet.univ)]
    show Integrable f ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set Space)))
    rw [← hrest]
    exact hsub
  have hψ : MeasurePreserving (fun q : ℝ × Space => (t - q.1, q.2))
      (volume.prod volume) (volume.prod volume) :=
    (volume.measurePreserving_sub_left t).prod (MeasurePreserving.id volume)
  have hemb : MeasurableEmbedding (fun q : ℝ × Space => (t - q.1, q.2)) :=
    ((Homeomorph.subLeft t).prodCongr (Homeomorph.refl Space)).measurableEmbedding
  have hpt : ∀ p : ℝ × Space, extInt T (Kd ν μ) t y i p = H (t - p.1, p.2) := by
    rintro ⟨s, z⟩
    by_cases hs : s < t
    · have h1 : s ∈ Iio t := hs
      have h2 : t - s ∈ Ioi (0 : ℝ) := sub_pos.mpr hs
      rw [hH, Set.indicator_of_mem (show (t - s, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Space) from
        ⟨h2, mem_univ _⟩)]
      simp only [extInt, Set.indicator_of_mem h1, hf, sub_sub_cancel]
    · have h1 : s ∉ Iio t := fun h => hs h
      have h3 : (t - s, z) ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space) := fun h => by
        have := h.1
        simp only [mem_Ioi] at this
        linarith
      rw [hH, Set.indicator_of_notMem h3]
      simp only [extInt, Set.indicator_of_notMem h1]
  have hcomp : Integrable (fun p : ℝ × Space => H (t - p.1, p.2)) (volume.prod volume) :=
    (hψ.integrable_comp_emb hemb).mpr hHint
  exact hcomp.congr (Filter.Eventually.of_forall fun p => (hpt p).symm)

end UnforcedLeray.Short.PartIIIb.Concrete
