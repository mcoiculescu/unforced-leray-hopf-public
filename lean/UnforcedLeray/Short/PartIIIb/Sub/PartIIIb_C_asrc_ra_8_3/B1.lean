import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# `VsumEqVc` (`PartIII-b:C/asrc/ra/8/3/1/1`)

Source: `the November 2 reference manuscript` 5029-5032, 4963-4977, 2040-2051.

`vsum ν s = ∑' k, Vj ν s k` (`PartIIIb.Concrete.vsum`, `ra_8.lean`) and `Vc ν c s = ∑' n, isoV ν s (·)`
(`Train.Vc = periodize`).  The two agree termwise after the coordinate equivalence `toVecL`, with
`c = cOf ν`, so the planar sum is the periodized vortex componentwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Termwise identity: the `k`-th Gaussian `V_k` of `ra_8` is the `Vec`-image of the isolated
vortex translated by `k cOf ν` (`Train.isoV`, `Train.width = 1 + νs`). -/
theorem vj_toVec_eq_isoV_B1 (ν s : ℝ) (k : ℤ) (y : ℝ × ℝ) :
    UnforcedLeray.Train.toVec (Vj ν s k y) =
      UnforcedLeray.Train.isoV ν s (y.1 - (k : ℝ) * cOf ν, y.2) := by
  rw [Vj, UnforcedLeray.Train.toVec_smul, UnforcedLeray.Train.isoV_apply, inv_pow]
  rfl

theorem vsumEqVc_proof : VsumEqVc := by
  unfold VsumEqVc
  intro ν s hν hs y
  have hν' : ν ≠ 0 := hν.ne'
  have hc : cOf ν ≠ 0 := inv_ne_zero (pow_ne_zero 2 hν')
  have hV : UnforcedLeray.Train.toVec (vsum ν s y) = UnforcedLeray.Train.Vc ν (cOf ν) s y := by
    unfold vsum
    rw [UnforcedLeray.Train.Vc, UnforcedLeray.Gaussian.periodize]
    rw [show UnforcedLeray.Train.toVec (∑' k : ℤ, Vj ν s k y) =
        ∑' k : ℤ, UnforcedLeray.Train.toVec (Vj ν s k y) from
      UnforcedLeray.Train.toVecL.map_tsum]
    exact tsum_congr fun k => vj_toVec_eq_isoV_B1 ν s k y
  refine Prod.ext ?_ ?_
  · show (vsum ν s y).1 = UnforcedLeray.Train.Vc ν (cOf ν) s y 0
    rw [← UnforcedLeray.Train.toVec_zero (vsum ν s y), hV]
  · show (vsum ν s y).2 = UnforcedLeray.Train.Vc ν (cOf ν) s y 1
    rw [← UnforcedLeray.Train.toVec_one (vsum ν s y), hV]

end UnforcedLeray.Short.PartIIIb.Concrete
