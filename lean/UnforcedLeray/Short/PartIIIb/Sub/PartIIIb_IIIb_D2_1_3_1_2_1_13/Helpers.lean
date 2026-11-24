import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13

/-!
# Helpers for the curl-route truncation steps (`L1`–`L4`)

Real-linear `crossC a` as a continuous linear map, phase-test closure of `curlT`,
and the `χₙ`-multiplied `curlT` (`TruncCutCurlTest`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- `v ↦ a × v` as a real-linear continuous map on `ℂ³`. -/
def crossCR (a : CVec3) : CVec3 →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => crossC a v
      map_add' := by
        intro u v
        ext i
        fin_cases i <;> simp [crossC] <;> ring
      map_smul' := by
        intro r v
        ext i
        fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring }

theorem crossCR_apply (a v : CVec3) : crossCR a v = crossC a v := rfl

theorem isPhaseTest_curlT {P : ℝ} {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) :
    IsPhaseTest P (curlT Ψ) := by
  have h : curlT Ψ = ∑ j : Fin 3, fun p => crossCR (EuclideanSpace.single j (1 : ℂ)) (dy j Ψ p) := by
    funext p
    simp [curlT, crossCR_apply, Finset.sum_apply]
  rw [h]
  exact IsPhaseTest.sum _ fun j _ => (hΨ.dy j).clm_comp (crossCR (EuclideanSpace.single j (1 : ℂ)))

/-- `χₙ • curl Ψ` is a phase test (`TruncCutCurlTest` in the Sub file). -/
theorem truncCutCurlTest_helper : TruncCutCurlTest := by
  intro P n Ψ hΨ
  have hc := isPhaseTest_curlT hΨ
  refine ⟨((contDiff_cutχ n).comp contDiff_snd).smul hc.smooth, ?_, ?_⟩
  · intro τ y
    simp [hc.periodic τ y]
  · obtain ⟨R, hR⟩ := hc.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

end UnforcedLeray.Short.PartIIIb.Concrete
