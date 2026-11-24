import UnforcedLeray.Lib.HeatCylinder.HeatVecH3GraphContraction
import UnforcedLeray.Lib.SobolevC.CylDensity

/-!
# Smooth vector representatives are dense in the centered H³ heat carrier

The generic cylinder density theorem supplies representatives up to cell-a.e. equality. This
leaf identifies each approximant with its actual `W.ofCylSmooth` class using value injectivity.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- Every centered vector H³ class is the limit of actual smooth periodic compact-axial vector
fields represented by their genuine `W.ofCylSmooth` elements. -/
theorem exists_smoothVectorH3_sequence {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    ∃ y : ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3,
      ∃ T : ℕ → Plane → Vec,
      ∃ hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n),
        (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) hc (T n) (hT n)) ∧
        Tendsto y atTop (𝓝 x) := by
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc (by norm_num) x
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
      (F := Vec) (k := 3) (p := 2) hc (T n) (hT n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.exists_smoothVectorH3_sequence
