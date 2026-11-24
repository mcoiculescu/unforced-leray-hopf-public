import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.PlanarSectors.NUE.PolarDefs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- **Conjugation of the angular sectors** (source 601-604: `f₂` is the angular-two sector). -/
theorem angularSectorConj :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.AngularSectorConj := by
  intro f r
  unfold UnforcedLeray.Planar.NUE.Polar.angularSector
  rw [map_mul]
  congr 1
  · simp [map_inv₀, map_mul, Complex.conj_ofReal, map_ofNat]
  · rw [intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_of_le (by positivity), ← integral_conj]
    congr 1
    funext θ
    have harg : conj (-(((-2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = -(((2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    simp only [map_mul]
    rw [← Complex.exp_conj, harg]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
