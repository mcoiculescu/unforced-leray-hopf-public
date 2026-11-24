import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2

/-!
# `OuterPairTransC` (task `PartIII-b:C/near/pins/3/4/2/3/2/1`)

Source `the November 2 reference manuscript` lines 3354, 3346-3352.
Transposition of the phase translation under the bilinear pairing `outerPair`:
`transC t` is composition with the measure-preserving shift `shiftT t`, and the shift
`shiftT (-t)` is measure preserving with inverse `shiftT t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0223 UnforcedLeray.PhaseSpace

theorem shiftT_inv_left {P : ℝ} [Fact (0 < P)] (t : ℝ) (z : PSpace P) :
    shiftT P t (shiftT P (-t) z) = z := by
  rw [← shiftT_add, neg_add_cancel]
  simp only [shiftT, AddCircle.coe_zero, Prod.mk_zero_zero, sub_zero]

theorem outerPairTransC : OuterPairTransC := by
  intro P _ t Ψ w
  have hemb : MeasurableEmbedding (shiftT P (-t)) :=
    (Homeomorph.subRight (0, ((-t : ℝ) : AddCircle P))).measurableEmbedding
  have hmp := mp_shiftT (P := P) (-t)
  have hL : outerPair Ψ (transC (E := SpaceC) t w) =
      ∫ z, dotL (Ψ z) (w (shiftT P t z)) := by
    unfold outerPair
    refine integral_congr_ae ?_
    filter_upwards [coeFn_transC (E := SpaceC) t w] with z hz
    rw [hz]
  have hR : outerPair (transC (E := SpaceC) (-t) Ψ) w =
      ∫ z, dotL (Ψ (shiftT P (-t) z)) (w z) := by
    unfold outerPair
    refine integral_congr_ae ?_
    filter_upwards [coeFn_transC (E := SpaceC) (-t) Ψ] with z hz
    rw [hz]
  rw [hL, hR]
  have key := hmp.integral_comp hemb (fun y => dotL (Ψ y) (w (shiftT P t y)))
  simp only [shiftT_inv_left] at key
  exact key.symm

end UnforcedLeray.Short.PartIIIb.NearInst
