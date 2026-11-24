import UnforcedLeray.Short.PartI.Sub.T02_2_4
import UnforcedLeray.Lib.Cylinder.ModesWirtinger

/-!
# Part I, task `PartI:T02/2/4` leaf: `SliceWirtinger`

Real form of the complex slice Wirtinger inequality `UnforcedLeray.Cyl.wirtinger_slice`
(`Lib/Cylinder/ModesWirtinger.lean`). Source of record:
`the November 2 reference manuscript`, line 447 (zero-mean Poincare/Wirtinger on
slices, `λ = 2π/c`).

Proof. Lift `g` to `f = ofReal ∘ g`, which is `C¹` and `c`-periodic. The `q`-average of `f` on
the slice is `c⁻¹ ·` the real integral of `g`, hence zero by the hypothesis. The complex
inequality then becomes the real one, with interval integrals turned into `Ioc` set integrals.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Complex
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

theorem sliceWirtinger : SliceWirtinger := by
  intro c g hc hg hper hmean η
  -- The complex lift `f = ofReal ∘ g`: `C¹` and `c`-periodic.
  have hf : ContDiff ℝ 1 (fun z : UnforcedLeray.Cyl.Plane => ((g z : ℝ) : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hg
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  have hperf : UnforcedLeray.Cyl.IsPeriodic c
      (fun z : UnforcedLeray.Cyl.Plane => ((g z : ℝ) : ℂ)) := by
    intro z
    show ((g (z.1 + c, z.2) : ℝ) : ℂ) = ((g z : ℝ) : ℂ)
    rw [hper z]
  -- The `q`-average of the lift vanishes on every slice.
  have hqavg : UnforcedLeray.Cyl.qAvg c (fun z : UnforcedLeray.Cyl.Plane => ((g z : ℝ) : ℂ)) η
      = 0 := by
    unfold UnforcedLeray.Cyl.qAvg
    show (c⁻¹ : ℂ) * ∫ q in Ico (-c / 2) (c / 2), ((g (q, η) : ℝ) : ℂ) = 0
    rw [integral_Ico_eq_integral_Ioc, integral_complex_ofReal, hmean η]
    simp
  -- The `q`-derivative of the lift is the lift of the `q`-derivative.
  have hd : ∀ q : ℝ, HasDerivAt (fun q' : ℝ => g (q', η))
      (UnforcedLeray.Cyl.partialQ g (q, η)) q := by
    intro q
    have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
    have hcomp : DifferentiableAt ℝ (fun q' : ℝ => g (q', η)) q :=
      (hgd (q, η)).comp q (by fun_prop)
    exact hcomp.hasDerivAt
  have hpf : ∀ q : ℝ,
      UnforcedLeray.Cyl.partialQ (fun z : UnforcedLeray.Cyl.Plane => ((g z : ℝ) : ℂ)) (q, η)
        = ((UnforcedLeray.Cyl.partialQ g (q, η) : ℝ) : ℂ) := by
    intro q
    have h2 := (hd q).ofReal_comp
    exact h2.deriv
  -- Apply the complex Wirtinger inequality on the slice.
  have hW := UnforcedLeray.Cyl.wirtinger_slice hc hf hperf η
  rw [hqavg] at hW
  simp only [hpf, sub_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hW
  have hc2 : -c / 2 ≤ c / 2 := by linarith
  simp only [intervalIntegral.integral_of_le hc2] at hW
  exact hW

end UnforcedLeray.Short.PartI
