import UnforcedLeray.Analysis.SpatialScaling
import UnforcedLeray.Consequences
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Spatial dilation on the actual L² quotient

An explicit map on Mathlib's L² equivalence classes is defined using their
measurable representatives. Its compatibility with any L² representative,
exact distance scaling, and continuity are proved. Thus continuity of the
viscosity-normalized velocity and derivative paths follows from the original
L² continuity, rather than being a transport hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace UnforcedLeray.ViscosityTransport

/-- Spatial scaling commutes with subtraction of actual fields. -/
private theorem spatialScale_sub_for_l2 (a b : ℝ) (f g : SpatialField) :
    SpatialScaling.spatialScale a b (f - g) =
      SpatialScaling.spatialScale a b f - SpatialScaling.spatialScale a b g := by
  ext x
  simp [SpatialScaling.spatialScale, smul_sub]

/-- Exact distance scaling in the genuine L² quotient. -/
theorem dist_toL2_spatialScale (a : ℝ) {b : ℝ} (hb : 0 < b)
    {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    dist (toL2 (SpatialScaling.spatialScale a b f))
      (toL2 (SpatialScaling.spatialScale a b g)) =
      (|a| * b ^ (-3 / 2 : ℝ)) * dist (toL2 f) (toL2 g) := by
  rw [dist_toL2 (SpatialScaling.memLp_spatialScale hf a hb.ne')
      (SpatialScaling.memLp_spatialScale hg a hb.ne'),
    ← spatialScale_sub_for_l2, SpatialScaling.l2Norm_spatialScale (f - g) (hf.sub hg) a hb,
    dist_toL2 hf hg]

/-- Quotient representatives convert back to the same L² element. -/
@[simp] theorem toL2_coe (f : L2Space) : toL2 (f : SpatialField) = f := by
  rw [toL2_of_memLp (Lp.memLp f)]
  exact Lp.toLp_coeFn f (Lp.memLp f)

/-- The actual dilation map on L² equivalence classes. -/
def dilationL2 (a b : ℝ) (f : L2Space) : L2Space :=
  toL2 (SpatialScaling.spatialScale a b (f : SpatialField))

/-- The definition does not depend on the choice of L² representative. -/
theorem dilationL2_toL2 (a : ℝ) {b : ℝ} (hb : 0 < b)
    {f : SpatialField} (hf : MemLp f 2 volume) :
    dilationL2 a b (toL2 f) = toL2 (SpatialScaling.spatialScale a b f) := by
  apply (toL2_eq_iff
    (SpatialScaling.memLp_spatialScale (Lp.memLp (toL2 f)) a hb.ne')
    (SpatialScaling.memLp_spatialScale hf a hb.ne')).2
  exact SpatialScaling.ae_eq_spatialScale (coeFn_toL2 hf) a hb.ne'

/-- Exact norm-distance scaling for all L² classes. -/
theorem dist_dilationL2 (a : ℝ) {b : ℝ} (hb : 0 < b) (f g : L2Space) :
    dist (dilationL2 a b f) (dilationL2 a b g) =
      (|a| * b ^ (-3 / 2 : ℝ)) * dist f g := by
  simpa only [dilationL2, toL2_coe] using
    dist_toL2_spatialScale a hb (Lp.memLp f) (Lp.memLp g)

/-- In particular, dilation is a bounded Lipschitz operator on L². -/
theorem lipschitz_dilationL2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    LipschitzWith ⟨|a| * b ^ (-3 / 2 : ℝ), by positivity⟩ (dilationL2 a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  exact (dist_dilationL2 a hb f g).le

theorem continuous_dilationL2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Continuous (dilationL2 a b) := (lipschitz_dilationL2 a hb).continuous

/-- Transport of genuine L² continuity along any parameter space and subset. -/
theorem continuousOn_toL2_spatialScale {X : Type*} [TopologicalSpace X]
    {u : X → SpatialField} {s : Set X}
    (hu_mem : ∀ t ∈ s, MemLp (u t) 2 volume)
    (hu : ContinuousOn (fun t => toL2 (u t)) s)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun t => toL2 (SpatialScaling.spatialScale a b (u t))) s := by
  have hc := (continuous_dilationL2 a hb).comp_continuousOn hu
  apply hc.congr
  intro t ht
  exact (dilationL2_toL2 a hb (hu_mem t ht)).symm

end UnforcedLeray.ViscosityTransport
