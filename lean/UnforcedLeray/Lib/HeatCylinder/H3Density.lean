import UnforcedLeray.Lib.SobolevC.CylDensity
import UnforcedLeray.Lib.TrainB.TensorBridge

/-!
# Smooth tensor representatives in cylinder H³

The generic cylinder density theorem supplies smooth representatives almost everywhere. This leaf
turns them into the actual `W.ofCylSmooth` sequence in the Euclidean row-tensor carrier, using
value injectivity rather than assuming the representatives are pointwise selected linearly.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- Every Euclidean row-tensor H³ class is the limit of actual smooth periodic compact-axial
`TensorVal` fields, represented by their genuine `W.ofCylSmooth` elements. -/
theorem exists_smoothTensorH3_sequence {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ∃ y : ℕ → UnforcedLeray.TrainB.TensorH3 c,
      ∃ T : ℕ → Plane → UnforcedLeray.TrainB.TensorVal,
      ∃ hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n),
        (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2)
          hc (T n) (hT n)) ∧
        Tendsto y atTop (𝓝 x) := by
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2)
    hc (by norm_num) x
  choose T hT hrep using hy
  refine ⟨y, T, hT, ?_, hlim⟩
  intro n
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have hrepW := (UnforcedLeray.Sob.ae_eq_wμ_iff
    (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
  filter_upwards [hrepW,
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2)
      hc (T n) (hT n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.exists_smoothTensorH3_sequence
