import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestComm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvSymm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdIBP

/-!
# Leaf `PartII-b:T12/1/1/2/37`: test-level symmetry of the planar Riesz pair

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
classical Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For tests `f, g`, `∫ S_{ik} f · g = ∫ f · S_{ik} g`. Two integrations by parts (`PdIBP`)
and the self-adjointness of the Newton potential on tests (`NewtonConvSymm`) move the two
derivatives of `S_{ik}` from `f` to `g`, and the result is `S_{ki} g = S_{ik} g`
(`RieszTestComm`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/37`.**  `∫ S_{ik} f · g = ∫ f · S_{ik} g` for tests `f, g`. -/
theorem rieszTestSymm : RieszTestSymm := by
  intro i k f g hf hg
  have hSm : ∀ (j : Fin 2) (u : Pl → ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ (pd j u) := by
    intro j u hu
    unfold pd
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hpi : IsTest (pd i g) := pdTest i g hg
  have hpk : IsTest (pd k f) := pdTest k f hf
  have hNpig : ContDiff ℝ ∞ (newtonConv (pd i g)) := newtonConvContDiff _ hpi
  have hNU : ContDiff ℝ ∞ (pd k (newtonConv f)) := hSm k _ (newtonConvContDiff f hf)
  -- integration by parts in `i`, moving `∂_i` from the kernel term onto `g`
  have e1 := pdIBP i (pd k (newtonConv f)) g hNU hg
  have e2 : pd k (newtonConv f) = newtonConv (pd k f) := newtonConvPd k f hf
  have e2' : ∫ x, pd i g x * pd k (newtonConv f) x =
      ∫ x, pd i g x * newtonConv (pd k f) x := by
    rw [e2]
  -- self-adjointness of the Newton potential on tests
  have e3 := newtonConvSymm (pd k f) (pd i g) hpk hpi
  have e3' : ∫ x, newtonConv (pd i g) x * pd k f x =
      ∫ x, pd k f x * newtonConv (pd i g) x := by
    congr 1
    funext x
    ring
  -- integration by parts in `k`
  have e4 := pdIBP k (newtonConv (pd i g)) f hNpig hf
  -- the right-hand side is `S_{ki} g = ∂_k (N * ∂_i g)`
  have e5 : pd i (newtonConv g) = newtonConv (pd i g) := newtonConvPd i g hg
  have e6 : rieszTest i k g = rieszTest k i g := rieszTestComm i k g hg
  have e7 : rieszTest k i g = pd k (newtonConv (pd i g)) := by
    unfold rieszTest
    rw [e5]
  have hRHS : ∫ x, f x * rieszTest i k g x = ∫ x, f x * pd k (newtonConv (pd i g)) x := by
    rw [e6, e7]
  have hLHS : ∫ x, rieszTest i k f x * g x =
      ∫ x, pd i (pd k (newtonConv f)) x * g x := rfl
  have hA : ∫ x, pd i (pd k (newtonConv f)) x * g x =
      ∫ x, g x * pd i (pd k (newtonConv f)) x := by
    congr 1
    funext x
    ring
  rw [hLHS, hRHS, hA]
  linarith [e1, e2', e3, e3', e4]

end UnforcedLeray.Short.IIb.PlaneRiesz
