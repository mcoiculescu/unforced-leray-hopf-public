import UnforcedLeray.Short.PartIIb.Sub.T12_6_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace UnforcedLeray.Short.IIb

theorem dsolDMeas : UnforcedLeray.Short.IIb.DsolDMeas := by
  unfold UnforcedLeray.Short.IIb.DsolDMeas
  intro c r ν μ G hc _hr1 _hr3 _hν _hμ hG σ H R _hσ
  obtain ⟨G', hG's, hae⟩ := exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  have h' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      0 < z.1 → G z = G' z := hae
  have hprod : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      0 < t → G (t, y) = G' (t, y) :=
    Measure.ae_ae_of_ae_prod h'
  have hgood : ∀ᵐ t ∂(volume : Measure ℝ), ∀ x : Coord,
      duhamelS.indicator (duhamelBody ν μ G) (x, t)
        = duhamelS.indicator (duhamelBody ν μ G') (x, t) := by
    classical
    filter_upwards [hprod] with t ht x
    by_cases hp : (x, t) ∈ duhamelS
    · have ht0 : 0 < t := (show t ∈ Ioo (0 : ℝ) x.1 from hp).1
      have hy : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), G (t, y) = G' (t, y) := by
        filter_upwards [ht] with y hy
        exact hy ht0
      have hflat : flatHeat (ν * (x.1 - t)) (fun z => G (t, z)) x.2 =
          flatHeat (ν * (x.1 - t)) (fun z => G' (t, z)) x.2 := by
        unfold flatHeat
        refine integral_congr_ae ?_
        filter_upwards [((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left x.2).quasiMeasurePreserving.ae
          hy] with w hw
        have hw' : G (t, x.2 - w) = G' (t, x.2 - w) := hw
        show flatHeatKernel (ν * (x.1 - t)) w • G (t, x.2 - w) =
          flatHeatKernel (ν * (x.1 - t)) w • G' (t, x.2 - w)
        rw [hw']
      rw [Set.indicator_apply, Set.indicator_apply, if_pos hp, if_pos hp]
      show (((t / x.1 : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) •
          flatHeat (ν * (x.1 - t)) (fun z => G (t, z)) x.2 =
        (((t / x.1 : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) •
          flatHeat (ν * (x.1 - t)) (fun z => G' (t, z)) x.2
      rw [hflat]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hp, if_neg hp]
  have hN : (volume : Measure ℝ) {t : ℝ | ¬ ∀ x : Coord,
      duhamelS.indicator (duhamelBody ν μ G) (x, t)
        = duhamelS.indicator (duhamelBody ν μ G') (x, t)} = 0 :=
    ae_iff.1 hgood
  have hprodnull : ((volume : Measure Coord).prod (volume : Measure ℝ))
      (univ ×ˢ {t : ℝ | ¬ ∀ x : Coord,
        duhamelS.indicator (duhamelBody ν μ G) (x, t)
          = duhamelS.indicator (duhamelBody ν μ G') (x, t)}) = 0 := by
    rw [Measure.prod_prod, hN, mul_zero]
  have hnull : (volume : Measure (Coord × ℝ)) {p : Coord × ℝ |
      ¬ (duhamelS.indicator (duhamelBody ν μ G) p = duhamelS.indicator (duhamelBody ν μ G') p)}
        = 0 := by
    show ((volume : Measure Coord).prod (volume : Measure ℝ)) _ = 0
    refine measure_mono_null ?_ hprodnull
    intro p hp
    exact ⟨mem_univ _, fun hall => hp (hall p.1)⟩
  have hae' : ∀ᵐ p ∂(volume : Measure (Coord × ℝ)),
      duhamelS.indicator (duhamelBody ν μ G) p = duhamelS.indicator (duhamelBody ν μ G') p :=
    ae_iff.2 hnull
  have hac : ((volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))).prod
      (volume : Measure ℝ)) ≪ (volume : Measure (Coord × ℝ)) := by
    show _ ≪ (volume : Measure Coord).prod (volume : Measure ℝ)
    exact Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      (Measure.absolutelyContinuous_of_le le_rfl)
  have hF' : StronglyMeasurable (duhamelS.indicator (duhamelBody ν μ G')) :=
    (stronglyMeasurable_duhamelBody ν μ hG's).indicator measurableSet_duhamelS
  refine hF'.aestronglyMeasurable.congr ?_
  have key : ∀ᵐ p ∂((volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))).prod
      (volume : Measure ℝ)),
      duhamelS.indicator (duhamelBody ν μ G) p = duhamelS.indicator (duhamelBody ν μ G') p :=
    hac.ae_le hae'
  filter_upwards [key] with p hp using hp.symm

end UnforcedLeray.Short.IIb
