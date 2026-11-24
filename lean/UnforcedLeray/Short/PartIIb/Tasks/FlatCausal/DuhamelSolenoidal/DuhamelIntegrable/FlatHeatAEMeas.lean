import UnforcedLeray.Short.PartIIb.Sub.T12_6_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIb

theorem flatHeatAEMeas : UnforcedLeray.Short.IIb.FlatHeatAEMeas := by
  unfold UnforcedLeray.Short.IIb.FlatHeatAEMeas
  intro θ g _hθ hg
  have hg0s : StronglyMeasurable (hg.mk g) := hg.stronglyMeasurable_mk
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), g x = hg.mk g x := hg.ae_eq_mk
  have hfeq : flatHeat θ g = flatHeat θ (hg.mk g) := by
    funext z
    unfold flatHeat
    apply integral_congr_ae
    have hqm := ((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving
    filter_upwards [hqm.ae hae] with w hw
    rw [hw]
  rw [hfeq]
  have hK : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => flatHeatKernel θ p.2) := by
    unfold flatHeatKernel
    fun_prop
  have hF : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      flatHeatKernel θ p.2 • (hg.mk g) (p.1 - p.2)) :=
    hK.stronglyMeasurable.smul (hg0s.comp_measurable (measurable_fst.sub measurable_snd))
  exact hF.integral_prod_right'.aestronglyMeasurable

end UnforcedLeray.Short.IIb
