import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff

/-!
# Leaf `PartII-b:T12/1/1/2/15`: the planar Riesz test pairs commute

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a test `f`, the Newton potential `u = N * f` is `C^∞` (`newtonConvContDiff`), and
`S_{ik} f = ∂_i ∂_k u`.  The second derivative of a `C²` function is symmetric, so
`∂_i ∂_k u = ∂_k ∂_i u`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The iterated partial derivative `∂_a ∂_b u` of a `C^∞` function `u` on the plane, at `x`,
is the second Fréchet derivative evaluated on the coordinate vectors. -/
theorem pd_pd_eq_fderiv_fderiv (u : Pl → ℝ) (hu : ContDiff ℝ ∞ u) (a b : Fin 2) (x : Pl) :
    pd a (pd b u) x = fderiv ℝ (fderiv ℝ u) x (Pi.single a 1) (Pi.single b 1) := by
  have hdiff : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hd := (hdiff x).hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single b (1 : ℝ)) x)
  show fderiv ℝ (fun y => fderiv ℝ u y (Pi.single b 1)) x (Pi.single a 1) =
    fderiv ℝ (fderiv ℝ u) x (Pi.single a 1) (Pi.single b 1)
  rw [hd.fderiv]
  simp

/-- **Leaf `PartII-b:T12/1/1/2/15`.** The Riesz test pairs `S_{ik}` commute on tests. -/
theorem rieszTestComm : RieszTestComm := by
  intro i k f hf
  have hu : ContDiff ℝ ∞ (newtonConv f) := newtonConvContDiff f hf
  unfold rieszTest
  funext x
  rw [pd_pd_eq_fderiv_fderiv (newtonConv f) hu i k x,
    pd_pd_eq_fderiv_fderiv (newtonConv f) hu k i x]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end UnforcedLeray.Short.IIb.PlaneRiesz
