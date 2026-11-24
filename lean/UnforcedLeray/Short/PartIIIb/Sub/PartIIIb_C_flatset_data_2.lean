import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1

/-!


Source `the November 2 reference manuscript`
lines 4565-4574 (`a(t) = 1 + νt ≤ 2.1` on `0 ≤ t ≤ 1.1/ν`; the periodic images of the Gaussian are at
distance `≥ c/2` from the cell, `c = ν⁻² ≥ 1`).

Reduction: `‖S.H t‖ = ‖HProf ν c t‖_{L²(cellMeasure)}` by `H_pin`, and the uniform `L²` bound
`PeriodizeL2Bound` (period `c ≥ 1`, Gaussian constant `A = 2.1`) together with the pointwise bound
`GaussPointBound` gives a bound independent of `ν ≤ 1` and of `t` in the band.  The two leaves are
shared with `GaussSourcesExist` (`PartIII-b_C_flatset_data_1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatSrcBdd_of (h1 : GaussPointBound) (h2 : GaussMeasurable) (h3 : PeriodizeL2Bound) :
    FlatSrcBdd := by
  intro m _
  obtain ⟨C, hC⟩ := h1 2.1 (by norm_num)
  obtain ⟨C3, hC3⟩ := h3 m 2.1 1 (by norm_num) one_pos
  have hmain : ∀ (ν : ℝ), 0 < ν → ν ≤ 1 → ∀ t ∈ Icc (0 : ℝ) (1.1 / ν),
      eLpNorm (HProf ν (cOf ν) t) 2 (B0579.cellMeasure (cOf ν) m) ≤ ENNReal.ofReal (C3 * C) ∧
      eLpNorm (RProf ν (cOf ν) t) 2 (B0579.cellMeasure (cOf ν) m) ≤ ENNReal.ofReal (C3 * C) := by
    intro ν hν hν1 t ht
    have hc1 : 1 ≤ cOf ν := by
      unfold cOf
      rw [one_le_inv₀ (by positivity)]
      nlinarith
    have hνt : ν * t ≤ 1.1 := by
      have := mul_le_mul_of_nonneg_left ht.2 hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    have hνt0 : 0 ≤ ν * t := mul_nonneg hν.le ht.1
    have hA : srcA ν t ∈ Icc (1 : ℝ) 2.1 := by
      unfold srcA ageA
      rw [max_eq_left ht.1]
      constructor <;> norm_num <;> linarith
    have hb := fun x => hC (srcA ν t) hA x
    obtain ⟨hmH, hmR⟩ := h2 (srcA ν t)
    exact ⟨(hC3 (cOf ν) hc1 (hMode (srcA ν t)) C hmH (fun x => (hb x).1)).2,
      (hC3 (cOf ν) hc1 (rMode (srcA ν t)) C hmR (fun x => (hb x).2)).2⟩
  refine ⟨max (C3 * C) 0, fun ν hν hν1 S t ht => ?_⟩
  obtain ⟨hH, hR⟩ := hmain ν hν hν1 t ht
  have hle : ENNReal.ofReal (C3 * C) ≤ ENNReal.ofReal (max (C3 * C) 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have e1 : ‖S.H t‖ = (eLpNorm (HProf ν (cOf ν) t) 2 (B0579.cellMeasure (cOf ν) m)).toReal := by
    have : ‖S.H t‖ = ‖((S.H t : Xmc (cOf ν) m) : XAmb (cOf ν) m)‖ := rfl
    rw [this, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (ae_cellMeasure_of_ae_cell (S.H_pin t))
  have e2 : ‖S.R t‖ = (eLpNorm (RProf ν (cOf ν) t) 2 (B0579.cellMeasure (cOf ν) m)).toReal := by
    have : ‖S.R t‖ = ‖((S.R t : Xmc (cOf ν) m) : XAmb (cOf ν) m)‖ := rfl
    rw [this, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (ae_cellMeasure_of_ae_cell (S.R_pin t))
  exact ⟨by rw [e1]; exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (hH.trans hle),
    by rw [e2]; exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (hR.trans hle)⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
