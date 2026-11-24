import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1_3

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace NullImageAux

/-- Lebesgue measure on `Coord × ℝ` is additive Haar (the instance is not found by search). -/
theorem coord4_haar : (volume : Measure (UnforcedLeray.Short.IIb.Coord × ℝ)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure (ℝ × (ℝ × ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure (ℝ × ℝ))
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure ℝ)

/-- A continuous linear equivalence between the two 4-dimensional spaces sends null sets to null
sets (the image measure of Lebesgue measure is a multiple of Lebesgue measure). -/
theorem cle_null (ψ : (ℝ × UnforcedLeray.Space) ≃L[ℝ] (UnforcedLeray.Short.IIb.Coord × ℝ))
    (t : Set (ℝ × UnforcedLeray.Space)) (ht : volume t = 0) :
    volume (ψ '' t) = 0 := by
  haveI := coord4_haar
  have hme : MeasurableEmbedding ψ := ψ.toHomeomorph.measurableEmbedding
  have hmap : Measure.map ψ volume (ψ '' t) = volume t := by
    rw [hme.map_apply, Set.preimage_image_eq t ψ.injective]
  have key := Measure.isAddLeftInvariant_eq_smul (volume : Measure (UnforcedLeray.Short.IIb.Coord × ℝ))
    (Measure.map ψ volume)
  rw [key, Measure.smul_apply, hmap, ht, smul_zero]

theorem finrank_eq_four :
    Module.finrank ℝ (ℝ × UnforcedLeray.Space) =
      Module.finrank ℝ (UnforcedLeray.Short.IIb.Coord × ℝ) := by
  simp [Module.finrank_prod, finrank_euclideanSpace, UnforcedLeray.Short.IIb.Coord]

end NullImageAux

open NullImageAux in
theorem null_image_dim4 : UnforcedLeray.Short.IIb.NullImageDim4 := by
  unfold UnforcedLeray.Short.IIb.NullImageDim4
  intro f s hf hs
  haveI := NullImageAux.coord4_haar
  let e0 : (ℝ × UnforcedLeray.Space) ≃ₗ[ℝ] (UnforcedLeray.Short.IIb.Coord × ℝ) :=
    LinearEquiv.ofFinrankEq _ _ finrank_eq_four
  let ψ : (ℝ × UnforcedLeray.Space) ≃L[ℝ] (UnforcedLeray.Short.IIb.Coord × ℝ) :=
    e0.toContinuousLinearEquiv
  have hψs : volume (ψ '' s) = 0 := cle_null ψ s hs
  have hmaps : MapsTo ψ.symm (ψ '' s) s := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hg : DifferentiableOn ℝ (fun y => f (ψ.symm y)) (ψ '' s) :=
    hf.comp ψ.symm.differentiableOn hmaps
  have key := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) hg hψs
  have himg : (fun y => f (ψ.symm y)) '' (ψ '' s) = f '' s := by
    simp [Set.image_image]
  rw [← himg]
  exact key
