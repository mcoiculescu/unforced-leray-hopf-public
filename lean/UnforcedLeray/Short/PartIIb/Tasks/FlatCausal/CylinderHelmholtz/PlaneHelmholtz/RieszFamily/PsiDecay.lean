import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLinear
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvGradDecay
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.DivTestIsTest

/-!
# Leaf `PartII-b:T12/1/1/2/30`: the Newton potential of a divergence decays like `1/|x|`

Source of record: `the November 2 reference manuscript`, lines 1670 (`P_0`, the
ordinary planar cylinder projection) and 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For test fields `F_k`, the potential `N * div F` equals `Σ_i ∂_i (N * F_i)` by linearity of the
Newton potential on tests and `∂_i (N * f) = N * ∂_i f`. Each summand is `O(1/|x|)` by
`newtonConvGradDecay`, so the sum is `O(1/|x|)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/30`.**  `N * div F = O(1/|x|)` for a test field `F`. -/
theorem psiDecay : UnforcedLeray.Short.IIb.PlaneRiesz.PsiDecay := by
  intro F hF
  have hpd : ∀ i : Fin 2, IsTest (pd i (F i)) := fun i => pdTest i (F i) (hF i)
  have hdiv : divTest F = pd 0 (F 0) + pd 1 (F 1) := by
    funext x
    simp [divTest, Fin.sum_univ_two]
  obtain ⟨C0, R0, h0⟩ := newtonConvGradDecay 0 (F 0) (hF 0)
  obtain ⟨C1, R1, h1⟩ := newtonConvGradDecay 1 (F 1) (hF 1)
  refine ⟨|C0| + |C1|, max R0 R1, fun x hx => ?_⟩
  have hsplit : newtonConv (divTest F) x
      = pd 0 (newtonConv (F 0)) x + pd 1 (newtonConv (F 1)) x := by
    calc newtonConv (divTest F) x
        = newtonConv (pd 0 (F 0) + pd 1 (F 1)) x := by rw [hdiv]
      _ = (newtonConv (pd 0 (F 0)) + newtonConv (pd 1 (F 1))) x := by
          rw [(newtonConvLinear (pd 0 (F 0)) (pd 1 (F 1)) (hpd 0) (hpd 1) 1).1]
      _ = newtonConv (pd 0 (F 0)) x + newtonConv (pd 1 (F 1)) x := rfl
      _ = pd 0 (newtonConv (F 0)) x + pd 1 (newtonConv (F 1)) x := by
          rw [newtonConvPd 0 (F 0) (hF 0), newtonConvPd 1 (F 1) (hF 1)]
  have hx0 : R0 ≤ ‖x‖ := le_trans (le_max_left _ _) hx
  have hx1 : R1 ≤ ‖x‖ := le_trans (le_max_right _ _) hx
  have a0 := h0 x hx0
  have a1 := h1 x hx1
  have ht : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
  rw [hsplit]
  calc |pd 0 (newtonConv (F 0)) x + pd 1 (newtonConv (F 1)) x|
      ≤ |pd 0 (newtonConv (F 0)) x| + |pd 1 (newtonConv (F 1)) x| := abs_add_le _ _
    _ ≤ C0 * ‖x‖⁻¹ + C1 * ‖x‖⁻¹ := add_le_add a0 a1
    _ ≤ (|C0| + |C1|) * ‖x‖⁻¹ := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (add_le_add (le_abs_self C0) (le_abs_self C1)) ht

end UnforcedLeray.Short.IIb.PlaneRiesz
