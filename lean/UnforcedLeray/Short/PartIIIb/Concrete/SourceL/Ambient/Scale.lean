import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9

/-!
# Exact scaling of `𝓛` (source 4783-4796)

For `ε > 0`: `W^mt_ε(y) = ε² V(εy)`, `χ_y` and `Ψ_Z` scale as in the source, so
`X^mt_ε(y) = ε² X^mt_1(εy)` and `𝓛_ε M(s) = ε³ 𝓛_1 M(s)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace Scale

theorem cylR_smul {ε : ℝ} (hε : 0 < ε) (y : Vec3) : cylR (ε • y) = ε * cylR y := by
  unfold cylR
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (ε * y 0) ^ 2 + (ε * y 1) ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

theorem rayPt_smul {ε : ℝ} (hε : 0 < ε) (y : Vec3) (u : ℝ) :
    rayPt (ε • y) (ε * u) = ε • rayPt y u := by
  rcases eq_or_ne (cylR y) 0 with hc | hc
  · ext i
    fin_cases i <;> simp [rayPt, cylR_smul hε, hc]
  · ext i
    fin_cases i <;> simp [rayPt, cylR_smul hε]
    · field_simp
    · field_simp

theorem chiYr_smul {ν ε : ℝ} (χy : ℝ → ℝ) (hε : 0 < ε) (r : ℝ) :
    chiYr ν ε χy r = chiYr ν 1 χy (ε * r) := by
  unfold chiYr
  by_cases hr : r = 0
  · simp [hr]
  · have h : ε * r ≠ 0 := mul_ne_zero hε.ne' hr
    simp [hr, h]

theorem deriv_chiYr_smul {ν ε : ℝ} (χy : ℝ → ℝ) (hε : 0 < ε) (r : ℝ) :
    deriv (chiYr ν ε χy) r = ε * deriv (chiYr ν 1 χy) (ε * r) := by
  have hfun : chiYr ν ε χy = fun r => chiYr ν 1 χy (ε * r) :=
    funext fun r => chiYr_smul χy hε r
  rw [hfun, deriv_comp_mul_left]
  simp [smul_eq_mul]

theorem streamPsi_smul {ε : ℝ} (hε : 0 < ε) (Z1 : Vec3 → Vec3) (y : Vec3) :
    streamPsi (fun w => ε ^ 2 • Z1 (ε • w)) y = streamPsi Z1 (ε • y) := by
  have h1 : ∫ ρ in Ioi (ε * cylR y), ρ * Z1 (rayPt (ε • y) ρ) 2
      = ε • ∫ u in Ioi (cylR y), (ε * u) * Z1 (rayPt (ε • y) (ε * u)) 2 := by
    have := integral_comp_mul_left_Ioi (fun ρ => ρ * Z1 (rayPt (ε • y) ρ) 2) (cylR y) hε
    rw [this, smul_inv_smul₀ hε.ne']
  unfold streamPsi
  rw [cylR_smul hε, neg_inj, h1, ← integral_smul]
  congr 1
  funext u
  rw [rayPt_smul hε]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem streamCut_smul {ν ε : ℝ} (χy : ℝ → ℝ) (hε : 0 < ε) (Z1 : Vec3 → Vec3) (y : Vec3) :
    streamCut ν ε χy (fun w => ε ^ 2 • Z1 (ε • w)) y
      = ε ^ 2 • streamCut ν 1 χy Z1 (ε • y) := by
  unfold streamCut
  rw [streamPsi_smul hε Z1 y, chiYr_smul χy hε (cylR y), deriv_chiYr_smul χy hε (cylR y),
    cylR_smul hε y]
  simp only [smul_add, smul_smul]
  congr 1
  · congr 1
    ring
  · congr 1
    rcases eq_or_ne (cylR y) 0 with hc | hc
    · simp [hc]
    · have hεne : ε ≠ 0 := hε.ne'
      field_simp

theorem Xmt_smul {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} {M : Chart → Mat3} (hε : 0 < ε) :
    Xmt c ν ε μ χo χy M = fun y => ε ^ 2 • Xmt c ν 1 μ χo χy M (ε • y) := by
  have hW : (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)
      = fun w => ε ^ 2 • ((youngW c ν 1 μ χo M - youngW c ν 1 (μ + 1) χo M) (ε • w)) := by
    funext w
    simp only [Pi.sub_apply, youngW, one_pow, one_smul, smul_sub]
  funext y
  unfold Xmt
  rw [hW, streamCut_smul χy hε]

theorem lptScale' (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (hε : 0 < ε) (s : ℝ) :
    Lpt c ν ε μ χo χy M s = ε ^ 3 • Lpt c ν 1 μ χo χy M s := by
  by_cases hs : 0 < s
  · unfold Lpt
    rw [if_pos hs, if_pos hs, Xmt_smul hε]
    have hp : ε • (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) = ![1⁻¹ / Real.sqrt s, 0, 0] := by
      have hεne : ε ≠ 0 := hε.ne'
      ext k
      fin_cases k <;> simp <;> field_simp
    have key : ∀ j : Fin 3,
        fderiv ℝ (fun y : Vec3 => ε ^ 2 • Xmt c ν 1 μ χo χy M (ε • y))
          ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1)
        = ε ^ 3 • fderiv ℝ (Xmt c ν 1 μ χo χy M) (ε • ![ε⁻¹ / Real.sqrt s, 0, 0])
            (Pi.single j 1) := by
      intro j
      have hfun : (fun y : Vec3 => ε ^ 2 • Xmt c ν 1 μ χo χy M (ε • y))
          = (ε ^ 2) • (fun y => Xmt c ν 1 μ χo χy M (ε • y)) := rfl
      rw [hfun, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_smul]
      congr 1
    funext i j
    rw [key j, hp]
    rfl
  · rw [Lpt_of_nonpos c ν ε μ χo χy M (not_lt.1 hs), Lpt_of_nonpos c ν 1 μ χo χy M (not_lt.1 hs),
      smul_zero]

theorem lptScale : LptScale := fun c ν ε μ χo χy M hε s => lptScale' c ν ε μ χo χy M hε s

end Scale

end UnforcedLeray.Short.PartIIIb.Concrete
