import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdIBP

/-!
# Leaf `PartII-b:T12/1/1/2/27`: integration by parts against a cutoff

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a smooth `ψ` and a test `χ`, the function `χ ∂_i ψ` is a test-times-smooth product.
Integration by parts in the direction `e_i` (`pdIBP`, with the test `χ ∂_iψ` and the smooth `ψ`)
and the product rule give, for each `i`,
`∫ χ (∂_iψ)² = -∫ ψ ∂_iχ ∂_iψ - ∫ χ ψ ∂_i²ψ`.  Summing over `i ∈ {0,1}` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- Product rule for the partial derivative `pd i` of a product of differentiable functions. -/
theorem pd_mul_eq (i : Fin 2) (g h : Pl → ℝ) (hg : Differentiable ℝ g)
    (hh : Differentiable ℝ h) (x : Pl) :
    pd i (fun y => g y * h y) x = g x * pd i h x + h x * pd i g x := by
  simp only [pd]
  rw [fderiv_fun_mul (hg x) (hh x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- `∂_i` maps smooth functions to smooth functions. -/
theorem pd_contDiff (i : Fin 2) (g : Pl → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (pd i g) := by
  unfold pd
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-- **Leaf `PartII-b:T12/1/1/2/27`.** Integration by parts against a test cutoff. -/
theorem cutoffIBP : CutoffIBP := by
  intro ψ χ hψ hχ
  obtain ⟨hχC, hχS⟩ := hχ
  have hχd : Differentiable ℝ χ := hχC.differentiable (by simp)
  have hχc : Continuous χ := hχC.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hpsi : ∀ i, ContDiff ℝ ∞ (pd i ψ) := fun i => pd_contDiff i ψ hψ
  have hpp : ∀ i, ContDiff ℝ ∞ (pd i (pd i ψ)) := fun i => pd_contDiff i _ (hpsi i)
  have hpχ : ∀ i, IsTest (pd i χ) := fun i => pdTest i χ ⟨hχC, hχS⟩
  -- integrability of the two families of integrands
  have hIntD : ∀ i : Fin 2, Integrable (fun x => χ x * ψ x * pd i (pd i ψ) x) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport
      ((hχc.mul hψc).mul (hpp i).continuous) ?_
    exact ((hχS.mul_right (f' := ψ)).mul_right (f' := pd i (pd i ψ)))
  have hIntE : ∀ i : Fin 2, Integrable (fun x => ψ x * pd i χ x * pd i ψ x) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport
      ((hψc.mul (hpχ i).1.continuous).mul (hpsi i).continuous) ?_
    exact (((hpχ i).2.mul_left (f := ψ)).mul_right (f' := pd i ψ))
  -- the per-direction identity
  have hi : ∀ i : Fin 2, ∫ x, χ x * (pd i ψ x) ^ 2 =
      -(∫ x, ψ x * pd i χ x * pd i ψ x) - ∫ x, χ x * ψ x * pd i (pd i ψ) x := by
    intro i
    have hfT : IsTest (fun x => χ x * pd i ψ x) :=
      ⟨hχC.mul (hpsi i), hχS.mul_right (f' := pd i ψ)⟩
    have h1 := pdIBP i ψ (fun x => χ x * pd i ψ x) hψ hfT
    beta_reduce at h1
    have hA : ∫ x, pd i (fun y => χ y * pd i ψ y) x * ψ x =
        ∫ x, (χ x * ψ x * pd i (pd i ψ) x + ψ x * pd i χ x * pd i ψ x) := by
      congr 1
      funext x
      rw [pd_mul_eq i χ (pd i ψ) hχd ((hpsi i).differentiable (by simp)) x]
      ring
    have hAdd := integral_add (hIntD i) (hIntE i)
    beta_reduce at hAdd
    have hB : ∫ x, χ x * pd i ψ x * pd i ψ x = ∫ x, χ x * (pd i ψ x) ^ 2 := by
      congr 1
      funext x
      ring
    linear_combination h1 - hA - hAdd - hB
  simp only [Fin.sum_univ_two]
  have hsumAdd := integral_add (hIntD 0) (hIntD 1)
  beta_reduce at hsumAdd
  have hsum : ∫ x, χ x * ψ x * (pd 0 (pd 0 ψ) x + pd 1 (pd 1 ψ) x) =
      ∫ x, (χ x * ψ x * pd 0 (pd 0 ψ) x + χ x * ψ x * pd 1 (pd 1 ψ) x) := by
    congr 1
    funext x
    ring
  rw [hi 0, hi 1]
  linear_combination hsum + hsumAdd

end UnforcedLeray.Short.IIb.PlaneRiesz
