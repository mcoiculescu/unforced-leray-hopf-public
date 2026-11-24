import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2

/-!
# `PhaseIntCell`: the normalised phase integral is `P⁻¹` times the cell integral

Source: `the November 2 reference manuscript` lines 1351-1362.
`phaseInt P G = P⁻¹ • ∫_{(0,P] × ℝ³} G` by Fubini on the product cell `Ioc 0 P ×ˢ univ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem phaseIntCell : PhaseIntCell := by
  intro P hP G hG
  have hG' : IntegrableOn G (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hG
  unfold phaseInt cellBase
  rw [Measure.volume_eq_prod, setIntegral_prod G hG']
  simp only [setIntegral_univ]
