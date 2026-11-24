import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2

/-!
# `AgeFiberNull`: age fibres `{p.1 = x}` are null for the age-weighted measure (source 3905-3912)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageFiberNull : AgeFiberNull := by
  intro c b x
  have hset : {p : Chart | p.1 = x} = ({x} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext p
    simp
  have h1 : (volume.restrict (Ioi (0 : ℝ))) {x} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  have h2 : ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ b)) {x} = 0 :=
    (withDensity_absolutelyContinuous _ _) h1
  unfold ageμ
  rw [hset, Measure.prod_prod, h2, zero_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
