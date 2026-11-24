import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# The planar Riesz kernel is the derivative of the gradient Newton kernel

Source of record: `the November 2 reference manuscript`, line 1670 (the planar
projection `P_0 = I - ∇Δ⁻¹ div`) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory, Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

For `z ≠ 0`, the partial derivative `∂_i` of the gradient kernel
`∂_k N(z) = (2π)⁻¹ z_k / |z|²` equals the planar Riesz kernel `K_{ik}(z)`.
The proof differentiates along the line `t ↦ z + t e_i`, where the quotient rule applies
because `|z|² ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- Derivative at `t = 0` of the line quotient `t ↦ c (x_k + tβ) / ((x₀ + tα₀)² + (x₁ + tα₁)²)`. -/
theorem hasDerivAt_gradKernel_line (xk β x0 x1 α0 α1 c : ℝ) (hD : x0 ^ 2 + x1 ^ 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => c * (xk + t * β) / ((x0 + t * α0) ^ 2 + (x1 + t * α1) ^ 2))
      (c * (β * (x0 ^ 2 + x1 ^ 2) - xk * (2 * x0 * α0 + 2 * x1 * α1)) / (x0 ^ 2 + x1 ^ 2) ^ 2) 0 := by
  have hn : HasDerivAt (fun t : ℝ => c * (xk + t * β)) (c * β) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const β).const_add xk).const_mul c
    simpa using h
  have ha : HasDerivAt (fun t : ℝ => x0 + t * α0) α0 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const α0).const_add x0
    simpa using h
  have hb : HasDerivAt (fun t : ℝ => x1 + t * α1) α1 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const α1).const_add x1
    simpa using h
  have hd : HasDerivAt (fun t : ℝ => (x0 + t * α0) ^ 2 + (x1 + t * α1) ^ 2)
      (2 * x0 * α0 + 2 * x1 * α1) 0 := by
    have h := (ha.pow 2).add (hb.pow 2)
    refine h.congr_deriv ?_
    norm_num
  have hne : (fun t : ℝ => (x0 + t * α0) ^ 2 + (x1 + t * α1) ^ 2) 0 ≠ 0 := by
    simpa using hD
  have hq := hn.div hd hne
  refine hq.congr_deriv ?_
  simp only [zero_mul, add_zero]
  ring

/-- **Leaf `PartII-b:T12/1/1/2/18`.** For `z ≠ 0` the derivative of `∂_k N` in direction `e_i`
is the planar Riesz kernel `K_{ik}(z) = (2π)⁻¹ (δ_{ik}|z|² - 2 z_i z_k)/|z|⁴`. -/
theorem planeRieszKernelEq : PlaneRieszKernelEq := by
  intro i k z hz
  have hD : z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by
    intro h
    apply hz
    have h0' : z 0 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (z 1), sq_nonneg (z 0)]) (sq_nonneg _)
    have h1' : z 1 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (z 1), sq_nonneg (z 0)]) (sq_nonneg _)
    have h0 : z 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp h0'
    have h1 : z 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1'
    funext j
    fin_cases j
    · simpa using h0
    · simpa using h1
  have hdiff : DifferentiableAt ℝ (newtonGradKernel k) z := by
    unfold newtonGradKernel
    fun_prop (disch := exact hD)
  set v : Fin 2 → ℝ := Pi.single i (1 : ℝ) with hv
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
    simpa using h
  have hcomp : HasDerivAt (newtonGradKernel k ∘ fun t : ℝ => z + t • v)
      (fderiv ℝ (newtonGradKernel k) z v) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdiff.hasFDerivAt hline (by simp)
  have hfun : (newtonGradKernel k ∘ fun t : ℝ => z + t • v) =
      fun t : ℝ => (2 * Real.pi)⁻¹ * (z k + t * v k) /
        ((z 0 + t * v 0) ^ 2 + (z 1 + t * v 1) ^ 2) := by
    funext t
    simp only [Function.comp, newtonGradKernel, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun] at hcomp
  have hA := hasDerivAt_gradKernel_line (z k) (v k) (z 0) (z 1) (v 0) (v 1) (2 * Real.pi)⁻¹ hD
  have heq := hcomp.unique hA
  rw [heq]
  unfold planeRieszKernel
  rw [if_neg hz]
  rw [hv]
  fin_cases i <;> fin_cases k <;> simp <;> ring

end UnforcedLeray.Short.IIb.PlaneRiesz
