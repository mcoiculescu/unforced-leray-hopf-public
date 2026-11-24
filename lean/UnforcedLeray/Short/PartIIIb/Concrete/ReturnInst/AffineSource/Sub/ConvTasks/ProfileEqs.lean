import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub

/-!
# `convProfileEqs`: the profile identities `rawPl = v + εHe`, `hatPl = h^p + εke`
(`PartIII-b:C/asrc/ra/9/2/2/7`)

Source 2075-2077 (`rawProfile = v + ε H e_z`), 4980 (`ĥ_A = √s[(h^p)_r e_r + ((h^p)_z + ε k) e_z]`).
For `s > 0` the factor `√s` cancels in `s^{-1/2} ĥ_A`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- The chart coefficient of `ĥ_A` for `s > 0`: `s^{-1/2} ĥ_A = (h^p_A + ε(0, k))` in `(r, z)`. -/
theorem hAcoef_eq_of_pos (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hs : 0 < s) :
    hAcoef ν ε χf A (s, x) =
      !₂[(hpA ν χf A s x).1,
        (hpA ν χf A s x).2 + ε * (psipA ν χf A s x - Kop (fun s' y => psipA ν χf A s' y) s x)] := by
  have hsqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  unfold hAcoef hhatA
  simp only [merOf, emb]
  rw [smul_smul, inv_mul_cancel₀ hsqrt, one_smul]
  ext i
  fin_cases i <;> simp

theorem convProfileEqs (as : ℝ) (χf : ℝ → ℝ) : ConvProfileEqs as χf := by
  intro p A s hs x
  constructor
  · refine Prod.ext ?_ ?_
    · simp [rawPl, plOf, trPl, trainPl, trHe, UnforcedLeray.Cons.C03.rawProfile_zero]
    · simp [rawPl, plOf, trPl, trainPl, trHe, trH, UnforcedLeray.Cons.C03.rawProfile_one]
  · refine Prod.ext ?_ ?_
    · simp [hatPl, plOf, hpPl, kEz, hAcoef_eq_of_pos _ _ _ _ _ _ hs]
    · simp [hatPl, plOf, hpPl, kEz, kPl, kOf, hAcoef_eq_of_pos _ _ _ _ _ _ hs]

end UnforcedLeray.Short.PartIIIb.Concrete
