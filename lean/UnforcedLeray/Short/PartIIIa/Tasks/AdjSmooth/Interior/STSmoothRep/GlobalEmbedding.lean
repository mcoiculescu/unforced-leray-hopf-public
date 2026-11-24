import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep.GlobalToEucl
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep.EuclEmbedding
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# `PartIII-a:T21/2/7/2/1/1/8/4`: `H^∞(ℝ × ℝ²) ⊂ C^k` (`stGlobalEmbedding`)

Transport of `euclGlobalEmbedding` along `toSpace`: for `f ∈ H^∞(ℝ × ℝ²)`, the function
`f ∘ toSpace` is in `H^∞(ℝ³)` (`stGlobalToEucl`), so it has a `C^k` version `G`; then
`G ∘ toSpace.symm` is `C^k` and a.e. equal to `f`, since `toSpace.symm` is measure preserving.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Sob

theorem measurePreserving_toSpace_symm : MeasurePreserving toSpace.symm volume volume := by
  let e : Eucl 3 ≃ᵐ STSpace := toSpace.toHomeomorph.toMeasurableEquiv
  have he : ⇑e = ⇑toSpace := rfl
  have h := (measurePreserving_toSpace).symm e
  have hs : ⇑e.symm = ⇑toSpace.symm := by
    funext p
    apply toSpace.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have := e.apply_symm_apply p
    rw [he] at this
    exact this
  rw [hs] at h
  exact h

theorem stGlobalEmbedding : STGlobalEmbedding := by
  intro f hf k
  obtain ⟨G, hGc, hGae⟩ := euclGlobalEmbedding (fun y => f (toSpace y)) (stGlobalToEucl f hf) k
  refine ⟨G ∘ toSpace.symm, hGc.comp toSpace.symm.contDiff, ?_⟩
  have h := (measurePreserving_toSpace_symm.quasiMeasurePreserving).ae_eq_comp hGae
  filter_upwards [h] with p hp
  simpa using hp

end UnforcedLeray.Short.IIIa
