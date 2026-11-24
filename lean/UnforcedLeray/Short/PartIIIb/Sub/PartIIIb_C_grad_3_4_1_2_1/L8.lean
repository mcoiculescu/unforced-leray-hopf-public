import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# `PartIII-b:C/grad/3/4/1/2/1/8`: the coefficient leaf `GCoefProp`

Source `the November 2 reference manuscript`
5063-5079.  If `Ay` is `C²` at `s > 0`, then `Ay` and `sDeriv Ay` are differentiable at `s`
with `∂_s(entry) = (s∂_s entry)/s`, and `sDeriv(sDeriv Ay) = s · ∂_s(sDeriv Ay)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gCoefProp : GCoefProp := by
  unfold GCoefProp
  intro Ay s hs hC i j
  have hdiff : DifferentiableAt ℝ Ay s := hC.differentiableAt (by norm_num)
  have hdD : DifferentiableAt ℝ (deriv Ay) s := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ Ay) s := hC.fderiv_right (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun t => fderiv ℝ Ay t 1) s := h1.clm_apply contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have hA : HasDerivAt Ay (deriv Ay s) s := hdiff.hasDerivAt
  have hid : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id' s
  have hm : HasDerivAt (fun t : ℝ => t • deriv Ay t)
      (s • deriv (deriv Ay) s + (1 : ℝ) • deriv Ay s) s :=
    hid.smul hdD.hasDerivAt
  have hsD : HasDerivAt (sDeriv Ay) (s • deriv (deriv Ay) s + (1 : ℝ) • deriv Ay s) s := hm
  have e1 : sDeriv Ay s i j / s = deriv Ay s i j := by
    show (s • deriv Ay s) i j / s = deriv Ay s i j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have e2 : sDeriv (sDeriv Ay) s i j / s = (s • deriv (deriv Ay) s + (1 : ℝ) • deriv Ay s) i j := by
    show (s • deriv (sDeriv Ay) s) i j / s = _
    rw [hsD.deriv]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) j
  · rw [e2]
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hsD i) j

end UnforcedLeray.Short.PartIIIb.Concrete
