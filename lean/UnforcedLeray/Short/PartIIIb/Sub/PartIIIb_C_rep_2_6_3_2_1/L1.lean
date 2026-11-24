import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1

/-!
# `kerIntShift` (`PartIII-b:C/rep/2/6/3/2/1/1`)

Source `the November 2 reference manuscript` lines 3611-3626.
The shift `s = t - h` is the measure-preserving map `(h,z) ↦ (t-h, z)` of `volume.prod volume`;
it turns the shifted integrand into the indicator of `Ioi 0` in the `h`-variable, and Fubini
gives the iterated integral defining `kerInt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem kerIntShift : KerIntShift := by
  intro T Φ t y i hint
  have hψ : MeasurePreserving (fun q : ℝ × Space => (t - q.1, q.2))
      (volume.prod volume) (volume.prod volume) :=
    (volume.measurePreserving_sub_left t).prod (MeasurePreserving.id volume)
  have hemb : MeasurableEmbedding (fun q : ℝ × Space => (t - q.1, q.2)) :=
    ((Homeomorph.subLeft t).prodCongr (Homeomorph.refl Space)).measurableEmbedding
  set K : ℝ × Space → ℂ := fun q => (Ioi (0 : ℝ)).indicator
    (fun h : ℝ => ∑ j : Fin 3, ∑ k : Fin 3,
      Φ h y q.2 i j k * ((T (t - h) q.2 j k : ℝ) : ℂ)) q.1 with hKdef
  have hK : ∀ q : ℝ × Space, extInt T Φ t y i (t - q.1, q.2) = K q := by
    rintro ⟨h, z⟩
    by_cases hh : 0 < h
    · have h1 : t - h ∈ Iio t := by simp only [mem_Iio]; linarith
      have h2 : h ∈ Ioi (0 : ℝ) := hh
      simp only [extInt, hKdef, Set.indicator_of_mem h1, Set.indicator_of_mem h2, sub_sub_cancel]
    · have h1 : t - h ∉ Iio t := by simp only [mem_Iio, not_lt]; linarith
      have h2 : h ∉ Ioi (0 : ℝ) := hh
      simp only [extInt, hKdef, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hKint : Integrable K (volume.prod volume) := by
    have h := (hψ.integrable_comp_emb hemb).mpr hint
    exact h.congr (Filter.Eventually.of_forall fun q => hK q)
  have e1 : ∫ p, extInt T Φ t y i p ∂(volume.prod volume) = ∫ q, K q ∂(volume.prod volume) := by
    rw [← hψ.integral_comp hemb (extInt T Φ t y i)]
    congr 1
    funext q
    exact hK q
  have hfub : ∫ q, K q ∂(volume.prod volume) = ∫ h in Ioi (0 : ℝ), ∫ z : Space,
      ∑ j : Fin 3, ∑ k : Fin 3, Φ h y z i j k * ((T (t - h) z j k : ℝ) : ℂ) := by
    rw [integral_prod K hKint]
    have hinner : ∀ h : ℝ, ∫ z : Space, K (h, z) = (Ioi (0 : ℝ)).indicator
        (fun h => ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
          Φ h y z i j k * ((T (t - h) z j k : ℝ) : ℂ)) h := by
      intro h
      by_cases hh : h ∈ Ioi (0 : ℝ)
      · simp only [hKdef, Set.indicator_of_mem hh]
      · simp only [hKdef, Set.indicator_of_notMem hh, integral_zero]
    simp_rw [hinner]
    rw [integral_indicator measurableSet_Ioi]
  unfold kerInt
  rw [e1, hfub]

end UnforcedLeray.Short.PartIIIb.Concrete
