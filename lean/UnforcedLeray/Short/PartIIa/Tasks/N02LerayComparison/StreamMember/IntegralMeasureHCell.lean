import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732 (the
Hilbert space `H = L²(s^{-3/2} ds dq dη)`, line 3307 of the old manuscript).  Proved by the

`integral_withDensity_eq_integral_toReal_smul` and `ENNReal.toReal_ofReal` on the cell (`s > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/---/
theorem integralMeasureHCell : IntegralMeasureHCell := by
  intro c G
  rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
    (ae_weightH_lt_top c), cellMeasure]
  refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), Complex.real_smul]

end UnforcedLeray.Short.PartIIa
