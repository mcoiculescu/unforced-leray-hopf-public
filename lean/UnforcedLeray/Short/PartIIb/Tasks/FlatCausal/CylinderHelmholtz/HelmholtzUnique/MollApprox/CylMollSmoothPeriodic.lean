import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt

/-!
# Leaf `T12/1/3/1/b`: smoothness and periodicity of the mollification

Proves `cylMollSmoothPeriodic : CylMollSmoothPeriodic` (SP 1923-1926). The mollification
`cylMoll ρ D` is the convolution `ρ.normed ⋆[lsmul] D` of a compactly supported smooth bump with a
locally integrable field (`cylLocInt`), hence `C^∞` (`HasCompactSupport.contDiff_convolution_left`).
Periodicity in `q` holds pointwise because `D` is `c`-periodic and the integrand is translated.
Components are obtained through the coordinate continuous linear map.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cylMollSmoothPeriodic : UnforcedLeray.Short.IIb.CylMollSmoothPeriodic := by
  intro c r hc hr D hD ρ
  have hper : ∀ z : ℝ × ℝ, D (z.1 + c, z.2) = D z := hD.1
  have hloc : LocallyIntegrable D volume := cylLocInt c r hc hr D hD
  have hconv : cylMoll ρ D =
      convolution (ρ.normed volume) D (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] CMerid →L[ℝ] CMerid) volume := by
    funext z
    simp only [cylMoll, convolution_def, ContinuousLinearMap.lsmul_apply]
  have hsm : ContDiff ℝ ∞ (cylMoll ρ D) := by
    rw [hconv]
    exact ρ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CMerid →L[ℝ] CMerid) ρ.contDiff_normed hloc
  have hperM : ∀ z : ℝ × ℝ, cylMoll ρ D (z.1 + c, z.2) = cylMoll ρ D z := by
    intro z
    unfold cylMoll
    congr 1
    funext y
    have h : ((z.1 + c, z.2) : ℝ × ℝ) - y = ((z - y).1 + c, (z - y).2) := by
      ext <;> simp <;> ring
    rw [h, hper (z - y)]
  refine ⟨hperM, fun i => ?_⟩
  let Li : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  exact Li.contDiff.comp hsm

end UnforcedLeray.Short.IIb
