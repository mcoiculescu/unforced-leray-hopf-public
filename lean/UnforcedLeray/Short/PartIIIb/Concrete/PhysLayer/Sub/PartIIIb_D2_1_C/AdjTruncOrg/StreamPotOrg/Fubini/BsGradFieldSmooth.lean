import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelWeakDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelLocInt
import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Smoothness and gradient of the Newton potential of a test function (BSGradFieldSmooth)

Source `the November 2 reference manuscript` (stream potential `psi = curl(Newton * Phi)`,
`curl psi = Phi`; the cited line range in the task spec, 1351-1362, is the free Cartesian equation).

With `g(z) = ∫ P(y - z) h(y) dy` and `P = 1/(4π|x|)` (even), `g = P ⋆ h` is a convolution of a
locally integrable kernel with a `C_c^∞` function, hence smooth. Its gradient is obtained from
`HasCompactSupport.hasFDerivAt_convolution_right`, and the weak derivative of `P` (`bsKernelWeakDeriv`)
identifies it with `∫ h(y) K(y - z) dy`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Newton potential `1/(4π|x|)` as a complex-valued kernel. -/
private abbrev newtonC (w : Space) : ℂ := ((UnforcedLeray.PressureAnalysis.newtonPotential w : ℝ) : ℂ)

private theorem newtonC_comm (y z : Space) : newtonC (z - y) = newtonC (y - z) := by
  unfold newtonC UnforcedLeray.PressureAnalysis.newtonPotential
  rw [norm_sub_rev]

private theorem newtonC_locInt : LocallyIntegrable newtonC volume := by
  have h2 := Complex.ofRealCLM.locallyIntegrableOn_comp
    (UnforcedLeray.PressureAnalysis.newtonPotential_locallyIntegrable.locallyIntegrableOn univ)
  rw [locallyIntegrableOn_univ] at h2
  have heq : newtonC = Complex.ofRealCLM ∘ UnforcedLeray.PressureAnalysis.newtonPotential := by
    funext w
    simp [newtonC]
  rw [heq]
  exact h2

/-- Reflection of the Newton convolution. -/
private theorem newtonC_reflect (F : Space → ℂ) (z : Space) :
    ∫ t : Space, newtonC t * F (z - t) = ∫ y : Space, newtonC (y - z) * F y := by
  calc ∫ t : Space, newtonC t * F (z - t)
      = ∫ y : Space, newtonC (z - y) * F (z - (z - y)) :=
        (integral_sub_left_eq_self (fun t : Space => newtonC t * F (z - t)) volume z).symm
    _ = ∫ y : Space, newtonC (y - z) * F y := by
        congr 1
        funext y
        rw [sub_sub_cancel, newtonC_comm]

private theorem newtonC_conv (h : Space → ℂ) (z : Space) :
    (newtonC ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] h) z = ∫ y : Space, newtonC (y - z) * h y := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  exact newtonC_reflect h z

/-- Integrability of `y ↦ g(y) • K(y - z)` for a continuous compactly supported `g`. -/
private theorem bsKernel_shift_integrable (g : Space → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (z : Space) :
    Integrable (fun y : Space => g y • bsKernel (y - z)) := by
  have h1 : Integrable (fun x : Space => g (x + z) • bsKernel x) := by
    have hcont : Continuous (fun x : Space => g (x + z)) := hg.comp (continuous_id.add continuous_const)
    have hcs : HasCompactSupport (fun x : Space => g (x + z)) :=
      hgc.comp_homeomorph (Homeomorph.addRight z)
    exact bsKernelLocInt.integrable_smul_left_of_hasCompactSupport hcont hcs
  have h2 := h1.comp_sub_right z
  simpa using h2

/-- The gradient of the convolution. -/
private theorem newtonC_fderiv (h : Space → ℂ) (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hc : HasCompactSupport h) (z : Space) (j : Fin 3) :
    fderiv ℝ (newtonC ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] h) z
        (EuclideanSpace.single j (1 : ℝ))
      = ∫ y : Space, newtonC (y - z) * fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ)) := by
  have hg1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast le_top)
  have hD := hc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ)
    newtonC_locInt hg1 z
  rw [hD.fderiv, convolution_precompR_apply (𝕜 := ℝ) (L := ContinuousLinearMap.mul ℝ ℂ) newtonC_locInt
    (hc.fderiv (𝕜 := ℝ)) (hh.continuous_fderiv (by simp)) z]
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  exact newtonC_reflect (fun y => fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))) z

/-- **Smoothness and gradient of the Newton convolution**. -/
theorem bsGradFieldSmooth : BSGradFieldSmooth := by
  intro h hh hc
  show (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Space => ∫ y : Space, newtonC (y - z) * h y)) ∧
    ∀ z : Space, bsGradS (fun z : Space => ∫ y : Space, newtonC (y - z) * h y) z =
      ∫ y : Space, h y • bsKernel (y - z)
  have hconv : (fun z : Space => ∫ y : Space, newtonC (y - z) * h y) =
      newtonC ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] h := by
    funext z
    exact (newtonC_conv h z).symm
  refine ⟨?_, fun z => ?_⟩
  · rw [hconv]
    exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) newtonC_locInt hh
  · have hwd : ∀ j : Fin 3, fderiv ℝ (fun z : Space => ∫ y : Space, newtonC (y - z) * h y) z
        (EuclideanSpace.single j (1 : ℝ)) = ∫ y : Space, bsKernel (y - z) j * h y := by
      intro j
      rw [hconv]
      rw [newtonC_fderiv h hh hc z j]
      exact bsKernelWeakDeriv h hh hc z j
    ext j
    simp only [bsGradS, PiLp.toLp_apply]
    rw [hwd j]
    have hint := bsKernel_shift_integrable h hh.continuous hc z
    have hcomp := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ) hint
    simp only [EuclideanSpace.coe_proj, PiLp.smul_apply, smul_eq_mul] at hcomp
    rw [← hcomp]
    congr 1
    funext y
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
