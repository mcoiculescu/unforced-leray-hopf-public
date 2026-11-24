import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelNewton
import UnforcedLeray.Analysis.Pressure.NewtonKernel
import UnforcedLeray.Statement

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `K` is locally integrable: each complex component is `-(newtonGradientKernel i)` and the
vector is the finite sum of the components times the coordinate vectors. -/
theorem bsKernelLocInt : BSKernelLocInt := by
  have hK : ∀ (w : Space) (i : Fin 3), bsKernel w i =
      ((-(UnforcedLeray.PressureAnalysis.newtonGradientKernel i w) : ℝ) : ℂ) := bsKernelNewton
  have hcomp : ∀ i : Fin 3, LocallyIntegrable (fun w : Space => bsKernel w i) := by
    intro i
    have h1 : LocallyIntegrable (fun w : Space =>
        -(UnforcedLeray.PressureAnalysis.newtonGradientKernel i w)) :=
      (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable i).neg
    have h2 := Complex.ofRealCLM.locallyIntegrableOn_comp (h1.locallyIntegrableOn univ)
    rw [locallyIntegrableOn_univ] at h2
    have heq : (fun w : Space => bsKernel w i) =
        Complex.ofRealCLM ∘ (fun w : Space =>
          -(UnforcedLeray.PressureAnalysis.newtonGradientKernel i w)) := by
      funext w
      simp [hK]
    rw [heq]
    exact h2
  have hterm : ∀ i : Fin 3, LocallyIntegrable (fun w : Space =>
      bsKernel w i • (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin 3))) := by
    intro i
    let L : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
      (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))
    have h3 := L.locallyIntegrableOn_comp ((hcomp i).locallyIntegrableOn univ)
    rw [locallyIntegrableOn_univ] at h3
    have heq : (fun w : Space => bsKernel w i • (EuclideanSpace.single i (1 : ℂ) :
        EuclideanSpace ℂ (Fin 3))) = L ∘ (fun w : Space => bsKernel w i) := by
      funext w
      simp [L]
    rw [heq]
    exact h3
  have hsum := locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hterm i)
  have heq : (fun w : Space => ∑ i : Fin 3, bsKernel w i •
      (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin 3))) = bsKernel := by
    funext w
    ext j
    simp [Pi.single_apply]
  unfold BSKernelLocInt
  rw [← heq]
  exact hsum

end UnforcedLeray.Short.PartIIIb.Concrete
