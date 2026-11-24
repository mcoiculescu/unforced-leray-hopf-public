import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLinear
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.DivTestIsTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestEqConvPd

/-!
# Leaf `PartII-b:T12/1/1/2/31`: the planar Riesz divergence identity `∂_i (N * div F) = Σ_k S_{ik} F_k`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0 = I - ∇Δ⁻¹div`,
the ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For planar tests `F_0, F_1`, the Newton potential of `div F = ∂_0 F_0 + ∂_1 F_1` splits by
linearity (`NewtonConvLinear`) into `N * ∂_0 F_0 + N * ∂_1 F_1`. Each summand is `C^∞`
(`NewtonConvContDiff`), so `∂_i` acts termwise, and `∂_i (N * ∂_k F_k) = S_{ik} F_k`
(`RieszTestEqConvPd`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- `∂_i` is additive at a point where both summands are differentiable. -/
theorem psiGrad_pd_add (i : Fin 2) (u v : Pl → ℝ) (x : Pl)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    pd i (fun y => u y + v y) x = pd i u x + pd i v x := by
  unfold pd
  have h : fderiv ℝ (fun y => u y + v y) x = fderiv ℝ u x + fderiv ℝ v x := fderiv_add hu hv
  rw [h, add_apply]

/-- **Leaf `PartII-b:T12/1/1/2/31`.**  `∂_i (N * div F) = Σ_k S_{ik} F_k` for planar tests `F`. -/
theorem psiGrad : PsiGrad := by
  intro F hF i
  funext x
  have hT0 : IsTest (pd 0 (F 0)) := pdTest 0 (F 0) (hF 0)
  have hT1 : IsTest (pd 1 (F 1)) := pdTest 1 (F 1) (hF 1)
  have hdiv : divTest F = pd 0 (F 0) + pd 1 (F 1) := by
    funext y
    simp [divTest, Fin.sum_univ_two]
  have hsplit : newtonConv (divTest F) =
      fun y => newtonConv (pd 0 (F 0)) y + newtonConv (pd 1 (F 1)) y := by
    rw [hdiv]
    funext y
    exact congrFun (newtonConvLinear (pd 0 (F 0)) (pd 1 (F 1)) hT0 hT1 1).1 y
  have hd0 : DifferentiableAt ℝ (newtonConv (pd 0 (F 0))) x :=
    ((newtonConvContDiff _ hT0).differentiable (by simp)).differentiableAt
  have hd1 : DifferentiableAt ℝ (newtonConv (pd 1 (F 1))) x :=
    ((newtonConvContDiff _ hT1).differentiable (by simp)).differentiableAt
  have h0 : rieszTest i 0 (F 0) = pd i (newtonConv (pd 0 (F 0))) :=
    rieszTestEqConvPd i 0 (F 0) (hF 0)
  have h1 : rieszTest i 1 (F 1) = pd i (newtonConv (pd 1 (F 1))) :=
    rieszTestEqConvPd i 1 (F 1) (hF 1)
  rw [hsplit, psiGrad_pd_add i _ _ x hd0 hd1, Fin.sum_univ_two, h0, h1]

end UnforcedLeray.Short.IIb.PlaneRiesz
