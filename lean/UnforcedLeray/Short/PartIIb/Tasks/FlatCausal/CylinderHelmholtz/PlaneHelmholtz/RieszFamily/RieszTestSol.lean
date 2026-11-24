import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLinear
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd

/-!
# Leaf `PartII-b:T12/1/1/2/39`: the summed Riesz pairs annihilate a solenoidal test field

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a solenoidal test field `Ψ` (`Σ_i ∂_i Ψ_i = 0`), `Σ_i S_{ki} Ψ_i = ∂_k (N * Σ_i ∂_i Ψ_i) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/39`.**  `Σ_i S_{ki} Ψ_i = 0` for a solenoidal test field `Ψ`. -/
theorem rieszTestSol : RieszTestSol := by
  intro Ψ hΨ hdiv k x
  have hpd : ∀ i : Fin 2, IsTest (pd i (Ψ i)) := fun i => pdTest i (Ψ i) (hΨ i)
  have hd : ∀ h : Pl → ℝ, IsTest h → Differentiable ℝ (newtonConv h) :=
    fun h hh => (newtonConvContDiff h hh).differentiable (by simp)
  have hpk : ∀ f g : Pl → ℝ, Differentiable ℝ f → Differentiable ℝ g → ∀ y,
      pd k (f + g) y = pd k f y + pd k g y := by
    intro f g hf hg y
    unfold pd
    rw [fderiv_add (hf y) (hg y)]
    rfl
  have hsum : ∀ i : Fin 2, rieszTest k i (Ψ i) = pd k (newtonConv (pd i (Ψ i))) := by
    intro i
    unfold rieszTest
    rw [newtonConvPd i (Ψ i) (hΨ i)]
  have hG : pd 0 (Ψ 0) + pd 1 (Ψ 1) = 0 := by
    funext y
    have hy := hdiv y
    simp only [divTest, Fin.sum_univ_two] at hy
    simpa [Pi.add_apply] using hy
  have hsum2 : newtonConv (pd 0 (Ψ 0)) + newtonConv (pd 1 (Ψ 1)) = 0 := by
    rw [← (newtonConvLinear (pd 0 (Ψ 0)) (pd 1 (Ψ 1)) (hpd 0) (hpd 1) 0).1, hG]
    funext z
    simp [newtonConv]
  rw [Fin.sum_univ_two, hsum 0, hsum 1]
  rw [← hpk (newtonConv (pd 0 (Ψ 0))) (newtonConv (pd 1 (Ψ 1)))
    (hd _ (hpd 0)) (hd _ (hpd 1)) x, hsum2]
  simp [pd]

end UnforcedLeray.Short.IIb.PlaneRiesz
