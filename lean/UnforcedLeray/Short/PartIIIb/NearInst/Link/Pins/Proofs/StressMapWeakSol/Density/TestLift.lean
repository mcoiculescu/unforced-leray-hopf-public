import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5_3

/-!
# `PartIII-b:C/near/pins/5/3/1`: `SWTestLift`, the real part of a smooth band test is a test

Source `the November 2 reference manuscript`
1660-1665 and 1678.  The map `x ↦ tv4 (tvLift (M₀ x))` is the componentwise real part of `M₀`
(`tv4_tvLift`).  Componentwise real part is a continuous real-linear map on `TensorVal`, so it
preserves smoothness; periodicity is pointwise; and the band condition passes because the
real part of `0` is `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIa

/-- Componentwise real part on tensors, real-linear. -/
def testReLin : TensorVal →ₗ[ℝ] TensorVal where
  toFun w := WithLp.toLp 2 fun i => (((w i).re : ℝ) : ℂ)
  map_add' w w' := by
    ext i
    simp
  map_smul' a w := by
    ext i
    simp

/-- Componentwise real part on tensors, continuous. -/
def testReL : TensorVal →L[ℝ] TensorVal := LinearMap.toContinuousLinearMap testReLin

theorem testReL_apply (w : TensorVal) (i : Fin 4) : testReL w i = (((w i).re : ℝ) : ℂ) := rfl

theorem tv4_tvLift_eq_testReL (a : TensorVal) : tv4 (tvLift a) = testReL a := by
  ext i
  rw [tv4_tvLift, testReL_apply]

theorem swTestLift : SWTestLift := by
  intro c M0 hM
  have hfun : (fun x => tv4 (tvLift (M0 x))) = fun x => testReL (M0 x) := by
    funext x
    exact tv4_tvLift_eq_testReL (M0 x)
  rw [hfun]
  refine ⟨?_, ?_, ?_⟩
  · exact testReL.contDiff.comp hM.smooth
  · intro p
    show testReL (M0 (p.1, p.2.1 + c, p.2.2)) = testReL (M0 p)
    rw [hM.periodic p]
  · obtain ⟨s0, s1, L, hs0, hband⟩ := hM.band
    refine ⟨s0, s1, L, hs0, fun p hp => hband p ?_⟩
    intro h0
    apply hp
    rw [h0, map_zero]

end UnforcedLeray.Short.PartIIIb.NearInst
