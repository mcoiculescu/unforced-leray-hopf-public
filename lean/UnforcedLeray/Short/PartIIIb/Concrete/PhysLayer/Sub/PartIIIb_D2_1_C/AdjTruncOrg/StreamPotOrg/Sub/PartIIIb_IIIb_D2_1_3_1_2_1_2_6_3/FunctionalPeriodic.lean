import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PotMeasPeriodic

/-!
# `FunctionalPeriodic`

`wgFun` is a.e. `P`-periodic in the phase. Source `the November 2 reference manuscript`
lines 1351-1362 and 1334-1337. The periodicity of `bsPot Φ` (`potMeasPeriodic`) and of `Dψ j`
(`IsInYr.periodic`) holds a.e. on the product; `Measure.ae_ae_of_ae_prod` gives, for a.e. `t`,
a.e. equality of the two integrands at `t + P` and `t`, and `integral_congr_ae` closes it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem functionalPeriodic : FunctionalPeriodic := by
  intro P Φ Dψ hW g j i
  have h1 : ∀ᵐ x : ℝ × Space, bsPot Φ (x.1 + P, x.2) = bsPot Φ x :=
    (potMeasPeriodic P hW.1 Φ hW.2.1).2
  have h2 : ∀ᵐ x : ℝ × Space, Dψ j (x.1 + P, x.2) = Dψ j x :=
    (hW.2.2 j).1.periodic
  rw [Measure.volume_eq_prod] at h1 h2
  have k1 := Measure.ae_ae_of_ae_prod h1
  have k2 := Measure.ae_ae_of_ae_prod h2
  filter_upwards [k1, k2] with t ht1 ht2
  have e1 : (∫ y : Space, fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * bsPot Φ (t + P, y) i) =
      ∫ y : Space, fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * bsPot Φ (t, y) i := by
    refine integral_congr_ae ?_
    filter_upwards [ht1] with y hy
    have hy' : bsPot Φ (t + P, y) = bsPot Φ (t, y) := hy
    rw [hy']
  have e2 : (∫ y : Space, g y * Dψ j (t + P, y) i) = ∫ y : Space, g y * Dψ j (t, y) i := by
    refine integral_congr_ae ?_
    filter_upwards [ht2] with y hy
    have hy' : Dψ j (t + P, y) = Dψ j (t, y) := hy
    rw [hy']
  unfold wgFun
  rw [e1, e2]

end UnforcedLeray.Short.PartIIIb.Concrete
