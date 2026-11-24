import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! Helpers for `velPhysCoefOf_of` (source 2666-2668, 2683): the ring chart of the lift returns
the field, by the periodicity of `F` in the phase and the identification of the chart point with
the meridional point. -/

/-- The chart similarity point is the meridional point `(ϱ y, 0, y₂)`; it ignores the phase slot. -/
theorem vpc_chartY (R : ℝ) (hR : 0 < R) (y : Space) (hy : y ∉ axis) (ζ η : ℝ)
    (hη : η = R * y 2 / ϱ y) :
    NearInst.chartY R (age R y, (ζ, η)) = meridPt y := by
  have hϱ : ϱ y ≠ 0 := (ϱ_pos hy).ne'
  have hsq : Real.sqrt (age R y) = R / ϱ y := sqrt_age hR hy
  unfold NearInst.chartY
  rw [hsq, hη]
  ext i
  fin_cases i <;> simp [meridPt] <;> field_simp

theorem velPhysCoefOf_of (R c : ℝ) : VelPhysCoefOf R c := by
  intro hR hc F hF hper x hx
  obtain ⟨τ, y⟩ := x
  have hx' : y ∉ axis := hx
  have hR0 : R ≠ 0 := hR.ne'
  have hs : 0 < age R y := age_pos hR0 hx'
  have hsq : 0 < Real.sqrt (age R y) := Real.sqrt_pos.2 hs
  have hcoef_eq : perExt c (coefOf R F) (Axi.chart R τ y) =
      (Real.sqrt (age R y))⁻¹ • !₂[F τ (meridPt y) 0, F τ (meridPt y) 2] := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, cellRep c (phase R τ y) = phase R τ y - c * k :=
      ⟨⌊(phase R τ y + c / 2) / c⌋, rfl⟩
    have hperiod : Function.Periodic (fun t => F t (meridPt y)) (2 * c / R) :=
      fun t => hper t (meridPt y)
    have hF2 : F (τ - (k : ℝ) * (2 * c / R)) (meridPt y) = F τ (meridPt y) :=
      hperiod.sub_int_mul_eq k
    have hτ : NearInst.chartTau R (age R y, (cellRep c (phase R τ y), trans R y)) =
        τ - (k : ℝ) * (2 * c / R) := by
      unfold NearInst.chartTau
      rw [hk]
      unfold phase
      field_simp
      ring
    have hY : NearInst.chartY R (age R y, (cellRep c (phase R τ y), trans R y)) =
        meridPt y := by
      exact vpc_chartY R hR y hx' _ _ rfl
    show coefOf R F (age R y, (cellRep c (phase R τ y), trans R y)) = _
    unfold coefOf
    rw [hτ, hY, hF2]
  show B0412.realC (Nv R (perExt c (coefOf R F)) τ y) = B0412.realC (F τ y)
  congr 1
  unfold Nv
  rw [hcoef_eq, map_smul, smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
  exact (hF τ y (mem_univ _) hx').symm

end UnforcedLeray.Short.PartIIIb.Concrete
