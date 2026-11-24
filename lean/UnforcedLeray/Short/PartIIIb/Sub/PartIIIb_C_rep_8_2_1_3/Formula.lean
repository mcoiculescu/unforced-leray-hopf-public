import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula.Hoop

/-!
# `RingFrameD2Formula` (`PartIII-b:C/rep/8/2/1/3/a`)

Source `the November 2 reference manuscript`
lines 5036-5045, 5463, 1206-1216.  The nine entries: the six line entries (`Entries.lean`), the
two symmetric ones, and the hoop-hoop entry (`Hoop.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi RingFrameD2FormulaAux RingChartRawD2Sub

theorem ringFrameD2Formula : RingFrameD2Formula := by
  intro R τ B y hR hy0 hy1 hB j l
  have hy := not_axis_az hy0
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  have hs := sqrt_chart_az (τ := τ) hR hy0 hy1
  have ha := chart_one_az (τ := τ) hR hy0 hy1
  have hy0' : y 0 ≠ 0 := hy0.ne'
  have h01 : physPd2 (Gf R τ B) 0 1 y = ringFrameD2 R⁻¹ B (chart R τ y) 0 1 := by
    rw [entry_01_raw hR hB hy0 hy1, ringFrameD2_01, hs, ha]
    ext i
    fin_cases i <;> simp [vecSp, coordinateVector_apply] <;> field_simp <;> (try simp) <;> (try ring)
  have h21 : physPd2 (Gf R τ B) 2 1 y = ringFrameD2 R⁻¹ B (chart R τ y) 2 1 := by
    rw [entry_21_raw hR hB hy0 hy1, ringFrameD2_21, hs]
    ext i
    fin_cases i <;> simp [vecSp, coordinateVector_apply] <;> field_simp <;> (try simp) <;> (try ring)
  have h11 : physPd2 (Gf R τ B) 1 1 y = ringFrameD2 R⁻¹ B (chart R τ y) 1 1 := by
    have h := entry_11_raw (τ := τ) hR hB hy0 hy1
    have h' : physPd2 (Gf R τ B) 1 1 y = (y 0)⁻¹ • ((Drho R⁻¹ B (chart R τ y) 0 -
        B (chart R τ y) 0 * (y 0)⁻¹) • (coordinateVector 0 : Space) +
        (Drho R⁻¹ B (chart R τ y) 1) • e3) := by
      rw [← h, smul_smul, inv_mul_cancel₀ hy0', one_smul]
    rw [h', ringFrameD2_11, hs, ha]
    ext i
    fin_cases i <;> simp [vecSp, coordinateVector_apply] <;> field_simp <;> (try simp) <;> (try ring)
  show physPd2 (Gf R τ B) j l y = _
  fin_cases j <;> fin_cases l
  · exact entry_00 hR hB hy0 hy1
  · exact h01
  · exact entry_02 hR hB hy0 hy1
  · rw [physPd2_symm hGa]; exact h01
  · exact h11
  · rw [physPd2_symm hGa]; exact h21
  · exact entry_20 hR hB hy0 hy1
  · exact h21
  · exact entry_22 hR hB hy0 hy1

end UnforcedLeray.Short.PartIIIb.Concrete
