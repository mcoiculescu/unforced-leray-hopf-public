import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLaplace

/-!
# Leaf `PartII-b:T12/1/1/2/38`: the gradient identity `Σ_i S_{ki} ∂_i φ = ∂_k φ` on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `φ` and `u = N * φ`, `S_{ki}(∂_iφ) = ∂_k ∂_i (N * ∂_i φ) = ∂_k ∂_i ∂_i u`
by `NewtonConvPd`.  Summing over `i`, `Σ_i ∂_i ∂_i u = Δu = φ` by `NewtonConvLaplace`, so the sum is
`∂_k φ`.  The sum commutes with `∂_k` because the summands are `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/38`.**  `Σ_i S_{ki} ∂_i φ = ∂_k φ` for a planar test `φ`. -/
theorem rieszTestGrad : RieszTestGrad := by
  intro φ hφ k x
  have hpd : ∀ (g : Pl → ℝ) (j : Fin 2), ContDiff ℝ ∞ g → ContDiff ℝ ∞ (pd j g) := by
    intro g j hg
    have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    exact hfd.clm_apply contDiff_const
  have hu : ContDiff ℝ ∞ (newtonConv φ) := newtonConvContDiff φ hφ
  have hadd : ∀ (j : Fin 2) (g h : Pl → ℝ), ContDiff ℝ ∞ g → ContDiff ℝ ∞ h →
      pd j (fun y => g y + h y) x = pd j g x + pd j h x := by
    intro j g h hg hh
    have hd : fderiv ℝ (fun y => g y + h y) x = fderiv ℝ g x + fderiv ℝ h x :=
      fderiv_add (hg.differentiable (by simp) x) (hh.differentiable (by simp) x)
    unfold pd
    rw [hd]
    rfl
  have hrw : ∀ i : Fin 2, rieszTest k i (pd i φ) = pd k (pd i (pd i (newtonConv φ))) := by
    intro i
    unfold rieszTest
    rw [← newtonConvPd i φ hφ]
  have h0 : ContDiff ℝ ∞ (pd 0 (pd 0 (newtonConv φ))) := hpd _ 0 (hpd _ 0 hu)
  have h1 : ContDiff ℝ ∞ (pd 1 (pd 1 (newtonConv φ))) := hpd _ 1 (hpd _ 1 hu)
  have hpsum : (fun y => pd 0 (pd 0 (newtonConv φ)) y + pd 1 (pd 1 (newtonConv φ)) y) = φ :=
    funext (fun y => newtonConvLaplace φ hφ y)
  calc ∑ i, rieszTest k i (pd i φ) x
      = ∑ i, pd k (pd i (pd i (newtonConv φ))) x := by
        simp only [hrw]
    _ = pd k (pd 0 (pd 0 (newtonConv φ))) x + pd k (pd 1 (pd 1 (newtonConv φ))) x := by
        rw [Fin.sum_univ_two]
    _ = pd k (fun y => pd 0 (pd 0 (newtonConv φ)) y + pd 1 (pd 1 (newtonConv φ)) y) x :=
        (hadd k _ _ h0 h1).symm
    _ = pd k φ x := by rw [hpsum]

end UnforcedLeray.Short.IIb.PlaneRiesz
