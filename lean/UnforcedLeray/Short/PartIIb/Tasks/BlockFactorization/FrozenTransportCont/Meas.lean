import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont.Flow

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIb.FrozenTransportContHelp

open PartIIbF23Sub

theorem volume_ac_pm (m : ℝ) : (volume : Measure B0579.Plane) ≪ planeMeasure m :=
  withDensity_absolutelyContinuous'
    (B0579.measurable_density m).coe_nnreal_ennreal.aemeasurable
    (Eventually.of_forall fun x => by simpa using (B0579.density_pos m x).ne')

theorem pm_ac_volume (m : ℝ) : planeMeasure m ≪ (volume : Measure B0579.Plane) :=
  withDensity_absolutelyContinuous _ _

instance pm_locFin (m : ℝ) : IsLocallyFiniteMeasure (planeMeasure m) :=
  IsLocallyFiniteMeasure.withDensity_coe (B0579.continuous_density m)

theorem flow_qmp (m : ℝ) (σ : ℝ) (hσ : 0 ≤ 1 + σ) (τ : ℝ) :
    Measure.QuasiMeasurePreserving (frozenRadialFlow σ τ) (planeMeasure m) (planeMeasure m) := by
  have hc : Continuous (frozenRadialFlow σ τ) := (contDiff_flow σ τ).continuous
  refine ⟨hc.measurable, ?_⟩
  intro s hs
  set t := toMeasurable (planeMeasure m) s with ht
  have ht0 : planeMeasure m t = 0 := by rw [ht, measure_toMeasurable]; exact hs
  have hpre : frozenRadialFlow σ τ ⁻¹' t = frozenRadialFlow σ (-τ) '' t := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, by rw [flow_add σ hσ, neg_add_cancel, flow_zero]⟩
    · rintro ⟨y, hy, rfl⟩
      show frozenRadialFlow σ τ (frozenRadialFlow σ (-τ) y) ∈ t
      rw [flow_add σ hσ, add_neg_cancel, flow_zero]; exact hy
  have h1 : (volume : Measure B0579.Plane) t = 0 := volume_ac_pm m ht0
  have h2 : (volume : Measure B0579.Plane) (frozenRadialFlow σ (-τ) '' t) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (volume : Measure B0579.Plane)
      (((contDiff_flow σ (-τ)).differentiable (by simp)).differentiableOn) h1
  have h3 : planeMeasure m (frozenRadialFlow σ τ ⁻¹' t) = 0 := by
    rw [hpre]; exact pm_ac_volume m h2
  refine le_antisymm ?_ (zero_le)
  calc Measure.map (frozenRadialFlow σ τ) (planeMeasure m) s
      ≤ Measure.map (frozenRadialFlow σ τ) (planeMeasure m) t := measure_mono (subset_toMeasurable _ _)
    _ = 0 := by rw [Measure.map_apply hc.measurable (measurableSet_toMeasurable _ _)]; exact h3

end UnforcedLeray.Short.IIb.FrozenTransportContHelp
