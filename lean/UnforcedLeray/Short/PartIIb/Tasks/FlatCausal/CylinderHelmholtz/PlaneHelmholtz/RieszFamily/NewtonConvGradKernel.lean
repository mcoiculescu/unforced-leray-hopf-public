import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelWeakDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Leaf `PartII-b:T12/1/1/2/11`: the gradient of the planar Newton potential of a test

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
classical Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f` and `k ∈ {0,1}`, `∂_k (N * f)(x) = ∫ ∂_kN(x - y) f(y) dy`.

Proof: `∂_k (N * f) = N * ∂_k f` (`NewtonConvPd`); then the substitution `y ↦ x - y` gives
`∫ N(z) ∂_k f(x - z) dz`; with the translate `ψ(z) = f(x - z)`, `∂_k ψ(z) = -∂_k f(x - z)` and
the weak derivative of the kernel (`NewtonKernelWeakDeriv`) moves the derivative to `N`; the
substitution is then reversed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

theorem newtonConvGradKernel : UnforcedLeray.Short.IIb.PlaneRiesz.NewtonConvGradKernel := by
  unfold NewtonConvGradKernel
  intro k f hf x
  have hpd : pd k (newtonConv f) x = newtonConv (pd k f) x :=
    congrFun (newtonConvPd k f hf) x
  rw [hpd]
  -- the translate `ψ z = f (x - z)` is a test function
  have hψ : IsTest (fun z : Pl => f (x - z)) := by
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (contDiff_const.sub contDiff_id)
    · exact hf.2.comp_homeomorph (Homeomorph.subLeft x)
  -- `∂_k ψ(z) = -∂_k f(x - z)`
  have hψpd : ∀ z : Pl, pd k (fun z : Pl => f (x - z)) z = -pd k f (x - z) := by
    intro z
    have hfd : HasFDerivAt f (fderiv ℝ f (x - z)) (x - z) :=
      ((hf.1.differentiable (by simp)) (x - z)).hasFDerivAt
    have hg : HasFDerivAt (fun w : Pl => x - w) (-ContinuousLinearMap.id ℝ Pl) z :=
      (hasFDerivAt_id z).const_sub x
    have hcomp := hfd.comp z hg
    have key : fderiv ℝ (fun w : Pl => f (x - w)) z =
        (fderiv ℝ f (x - z)).comp (-ContinuousLinearMap.id ℝ Pl) := hcomp.fderiv
    simp only [pd]
    rw [key]
    simp
  -- Step A: substitution `y ↦ x - y`
  have hA : ∫ y, newtonKernel (x - y) * pd k f y =
      ∫ z, newtonKernel z * pd k f (x - z) := by
    have h := integral_sub_left_eq_self
      (fun z : Pl => newtonKernel z * pd k f (x - z)) volume x
    simp only [sub_sub_cancel] at h
    exact h
  -- Step B: move the derivative onto the kernel (weak derivative)
  have hB : ∫ z, newtonKernel z * pd k f (x - z) =
      ∫ z, newtonGradKernel k z * f (x - z) := by
    have h1 : ∀ z : Pl, newtonKernel z * pd k f (x - z) =
        -(newtonKernel z * pd k (fun z : Pl => f (x - z)) z) := by
      intro z
      rw [hψpd z]
      ring
    have hweak := newtonKernelWeakDeriv k (fun z : Pl => f (x - z)) hψ
    simp only [h1, integral_neg]
    rw [hweak]
    simp
  -- Step C: substitution `z ↦ x - z` back
  have hC : ∫ z, newtonGradKernel k z * f (x - z) =
      ∫ y, newtonGradKernel k (x - y) * f y := by
    have h := integral_sub_left_eq_self
      (fun z : Pl => newtonGradKernel k z * f (x - z)) volume x
    simp only [sub_sub_cancel] at h
    exact h.symm
  unfold newtonConv
  rw [hA, hB, hC]

end UnforcedLeray.Short.IIb.PlaneRiesz
