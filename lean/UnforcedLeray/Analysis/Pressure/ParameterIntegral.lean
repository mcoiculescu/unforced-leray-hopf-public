import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Joint measurability of the literal spatial potential

A measurable spatial kernel and an almost everywhere jointly measurable
forcing produce an almost everywhere jointly measurable parameter integral.
The proof keeps the actual forcing, using a measurable representative only
to establish measurability and then proving equality of the literal integrals.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
namespace UnforcedLeray.PressureAnalysis

/-- Joint measurability of a spatial convolution depending on time. -/
theorem parameter_convolution_aestronglyMeasurable
    {μ : Measure ℝ} {K : Space → ℝ} {F : SpaceTime → ℝ}
    (hK : Measurable K) (hF : AEStronglyMeasurable F (μ.prod volume)) :
    AEStronglyMeasurable
      (fun z : SpaceTime => ∫ y : Space, K (z.2 - y) * F (z.1, y))
      (μ.prod volume) := by
  have hK' : StronglyMeasurable
      (fun z : SpaceTime × Space => K (z.1.2 - z.2)) :=
    hK.stronglyMeasurable.comp_measurable (measurable_fst.snd.sub measurable_snd)
  have hF' : StronglyMeasurable
      (fun z : SpaceTime × Space => hF.mk F (z.1.1, z.2)) :=
    hF.stronglyMeasurable_mk.comp_measurable
      (measurable_fst.fst.prodMk measurable_snd)
  have hP' : StronglyMeasurable
      (fun z : SpaceTime => ∫ y : Space, K (z.2 - y) * hF.mk F (z.1, y)) :=
    (hK'.mul hF').integral_prod_right'
  apply hP'.aestronglyMeasurable.congr
  have hslice : ∀ᵐ t ∂μ, ∀ᵐ y ∂(volume : Measure Space), F (t,y) = hF.mk F (t,y) :=
    ae_ae_of_ae_prod hF.ae_eq_mk
  have hpull : ∀ᵐ z ∂μ.prod (volume : Measure Space),
      ∀ᵐ y ∂(volume : Measure Space), F (z.1,y) = hF.mk F (z.1,y) :=
    quasiMeasurePreserving_fst.ae hslice
  filter_upwards [hpull] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  rw [hy]

end UnforcedLeray.PressureAnalysis
