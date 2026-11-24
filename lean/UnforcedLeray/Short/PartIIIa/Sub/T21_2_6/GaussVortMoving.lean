import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# Part III-a, `PartIII-a:T21/2/6/5`: the Gaussian vorticity on the moving cell

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2867
and 3050-3051. Given the scaling identity `DatumCurlScale` (SP 2866-2867) and the weighted
bound `DatumCurlWeighted` for the periodized unit Gaussian vorticity (SP 2866-2867), the weighted
bound of the Gaussian part of the rescaled vorticity on the moving cell `C_d`, `d = c/√a ≥ 1`,
follows by multiplying the scaling factor `(a² (√a)^j)⁻¹` into the weighted sup bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The Gaussian part of the rescaled vorticity on the moving cell** (SP 2866-2867, 3050-3051),
assembled from the scaling identity and the weighted bound of the datum. -/
theorem gaussVortMoving_of (hS : DatumCurlScale) (hW : DatumCurlWeighted) : GaussVortMoving := by
  unfold GaussVortMoving DatumCurlWeighted at *
  intro k j
  obtain ⟨C, hC⟩ := hW k j
  refine ⟨C, fun ν c s hν hc hs hle y hy => ?_⟩
  set a : ℝ := clockA ν s with ha_def
  have ha_pos : 0 < a := by
    have : 0 ≤ ν * s := mul_nonneg hν.le hs
    rw [ha_def]
    unfold clockA
    linarith
  have hsqrt_pos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha_pos
  have hsqrt_le : Real.sqrt a ≤ c := by
    calc Real.sqrt a ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hle
      _ = c := Real.sqrt_sq hc.le
  have hd : 1 ≤ cellLen c a := by
    unfold cellLen
    exact (one_le_div hsqrt_pos).2 hsqrt_le
  have hbound := hC (cellLen c a) hd y hy
  unfold DatumCurlScale at hS
  have hscale := hS ν c s hν hc hs j y
  have hinv : 0 ≤ (a ^ 2 * Real.sqrt a ^ j)⁻¹ := by positivity
  have hjpos : 0 < B0579.jb y := by
    unfold B0579.jb
    nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  have hjk : 0 ≤ B0579.jb y ^ k := pow_nonneg hjpos.le k
  calc B0579.jb y ^ k *
        ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c s))
          (Real.sqrt a * y.1, Real.sqrt a * y.2)‖
      ≤ B0579.jb y ^ k * ((a ^ 2 * Real.sqrt a ^ j)⁻¹ *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (cellLen c a))) y‖) :=
        mul_le_mul_of_nonneg_left hscale hjk
    _ = (a ^ 2 * Real.sqrt a ^ j)⁻¹ *
          (B0579.jb y ^ k *
            ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (cellLen c a))) y‖) := by
        ring
    _ ≤ (a ^ 2 * Real.sqrt a ^ j)⁻¹ * C := mul_le_mul_of_nonneg_left hbound hinv
    _ = C * (a ^ 2 * Real.sqrt a ^ j)⁻¹ := by ring

end UnforcedLeray.Short.IIIa
