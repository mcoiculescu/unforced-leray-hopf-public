import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1

/-!
# Proof of `SCPsiSubst` (source 4178-4186, 4917-4937)

Change of variables `ρ = r t` with `r = cylR y > 0`:
`∫ ρ in (r,∞), ρ Z_z(rayPt y ρ) dρ = r² ∫ t in (1,∞), t Z_z(t y₀, t y₁, y₂) dt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scPsiSubst : SCPsiSubst := by
  unfold SCPsiSubst
  intro Z y hy
  have hr0 : 0 < cylR y := hy
  have hsq : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold cylR
    exact Real.sq_sqrt (by positivity)
  have hpt : ∀ t : ℝ, rayPt y (cylR y * t) = ![t * y 0, t * y 1, y 2] := by
    intro t
    funext i
    fin_cases i
    · simp [rayPt]
      field_simp
    · simp [rayPt]
      field_simp
    · simp [rayPt]
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (fun ρ : ℝ => ρ * Z (rayPt y ρ) 2) 1 hr0
  simp only [mul_one, smul_eq_mul] at hsub
  have hfun : (fun t : ℝ => (cylR y * t) * Z (rayPt y (cylR y * t)) 2)
      = fun t : ℝ => cylR y * psiF Z t y := by
    funext t
    rw [hpt t]
    unfold psiF
    ring
  have hL : ∫ ρ in Ioi (cylR y), ρ * Z (rayPt y ρ) 2
      = cylR y * ∫ t in Ioi (1 : ℝ), (cylR y * t) * Z (rayPt y (cylR y * t)) 2 := by
    rw [hsub]
    field_simp
  unfold streamPsi
  rw [hL, hfun, MeasureTheory.integral_const_mul, ← hsq]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
