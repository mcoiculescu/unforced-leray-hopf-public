import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.AziDef
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonVEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# `PartIII-b:C/rep/8/1/1/2/4/org`: the ray symmetry of the zero-width young field — proof

Source `the November 2 reference manuscript`
lines 4771-4784, 4917-4937.  `rayPt w ρ` is the rotation by the azimuth `θ = arg(w₁ + i w₂)` of
`(ρ, 0, w₃)`, rotations commute with the scaling `y ↦ εy`, and `V_μ(R_θx) = R_θV_μ(x)` off the old
source disc (`newtonVEquivariant`); the rotation fixes the vertical component.

This file must not import the `rep_8_1` chain (`PartIII-b_C_rep_8_1_org.lean` and
`SourceL/Sub/PartIII-b_C_srcL_7.lean` both declare `cylR_rayPt`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace GeomYAAzi

theorem youngW_rayPt_two {c ν ε μ : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hμ : 0 < μ) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (w : Vec3)
    (hw : 0 < cylR w) (ρ : ℝ) (hρ : 5 * ν / 6 < (ε * ρ) ^ 2) :
    youngW c ν ε μ χo M (rayPt w ρ) 2 = youngW c ν ε μ χo M ![ρ, 0, w 2] 2 := by
  set z : ℂ := ⟨w 0, w 1⟩ with hzdef
  have hnorm : ‖z‖ = cylR w := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rfl
  have hz : z ≠ 0 := by
    intro h0
    have : ‖z‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm] at this
    exact hw.ne' this
  set θ := Complex.arg z
  have hcos : Real.cos θ = w 0 / cylR w := by
    rw [Complex.cos_arg hz, hnorm]
  have hsin : Real.sin θ = w 1 / cylR w := by
    rw [Complex.sin_arg, hnorm]
  have hrot : rayPt w ρ = rotAx θ ![ρ, 0, w 2] := by
    funext i
    fin_cases i <;> simp [rayPt, rotAx, hcos, hsin] <;> ring
  have hreg : 5 * ν / 6 <
      (ε • (![ρ, 0, w 2] : Vec3)) 0 ^ 2 + (ε • (![ρ, 0, w 2] : Vec3)) 1 ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero]
    nlinarith
  have hV := newtonVEquivariant c ν μ χo M hc hν hμ hχ hM θ (ε • ![ρ, 0, w 2]) hreg
  unfold youngW
  rw [hrot, ← rotAx_smul, hV]
  simp [rotAx]

end GeomYAAzi

/-- **`YoungWRayAzi`** (source 4771-4784, 4917-4937), from `newtonVEquivariant`. -/
theorem youngWRayAzi : YoungWRayAzi :=
  fun _ _ _ _ _ _ hc hν hμ hχ hM w hw ρ hρ => GeomYAAzi.youngW_rayPt_two hc hν hμ hχ hM w hw ρ hρ

end UnforcedLeray.Short.PartIIIb.Concrete
