import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLinear

/-!
# Leaf `PartII-b:T12/1/1/2/17`: linearity of the test-level Riesz pair `f ↦ S_{ik} f`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

`S_{ik} f = ∂_i ∂_k (N * f)`.  The Newton potential is linear on tests and smooth, so the
partial derivatives are additive and homogeneous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The partial derivative of a `C^∞` function is `C^∞`. -/
theorem rtl_pd_contDiff (i : Fin 2) (g : Pl → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (pd i g) := by
  unfold pd
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-- `∂_k (u + v) = ∂_k u + ∂_k v` for `C^∞` functions `u, v`. -/
theorem rtl_pd_add (k : Fin 2) (u v : Pl → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    pd k (u + v) = pd k u + pd k v := by
  funext x
  show fderiv ℝ (u + v) x (Pi.single k 1) = fderiv ℝ u x (Pi.single k 1) + fderiv ℝ v x (Pi.single k 1)
  exact congrArg (fun L : Pl →L[ℝ] ℝ => L (Pi.single k 1))
    (fderiv_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x))

/-- `∂_k (c • u) = c • ∂_k u` for a `C^∞` function `u`. -/
theorem rtl_pd_smul (k : Fin 2) (c : ℝ) (u : Pl → ℝ) (hu : ContDiff ℝ ∞ u) :
    pd k (c • u) = c • pd k u := by
  funext x
  show fderiv ℝ (c • u) x (Pi.single k 1) = c • fderiv ℝ u x (Pi.single k 1)
  exact congrArg (fun L : Pl →L[ℝ] ℝ => L (Pi.single k 1))
    (fderiv_const_smul (hu.differentiable (by simp) x) c)

/-- **Leaf `PartII-b:T12/1/1/2/17`.**  `f ↦ S_{ik} f` is linear on tests. -/
theorem rieszTestLinear : RieszTestLinear := by
  intro i k f g hf hg c
  have hNf : ContDiff ℝ ∞ (newtonConv f) := newtonConvContDiff f hf
  have hNg : ContDiff ℝ ∞ (newtonConv g) := newtonConvContDiff g hg
  constructor
  · unfold rieszTest
    rw [(newtonConvLinear f g hf hg c).1, rtl_pd_add k _ _ hNf hNg,
      rtl_pd_add i _ _ (rtl_pd_contDiff k _ hNf) (rtl_pd_contDiff k _ hNg)]
  · unfold rieszTest
    rw [(newtonConvLinear f f hf hf c).2, rtl_pd_smul k c _ hNf,
      rtl_pd_smul i c _ (rtl_pd_contDiff k _ hNf)]

end UnforcedLeray.Short.IIb.PlaneRiesz
