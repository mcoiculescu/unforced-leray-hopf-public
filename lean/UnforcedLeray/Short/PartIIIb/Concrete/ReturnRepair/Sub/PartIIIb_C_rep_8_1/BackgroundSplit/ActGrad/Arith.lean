import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad.Pointwise

/-!
# `ActGrad` helpers: coefficient bookkeeping (source 5212-5217, 5282-5289)

Elementary facts used by the assembly of `ActGrad`: monotone collection of `ℝ≥0∞` majorants with
real coefficients, the meridional reading of an annulus profile, and the physical rescaling
`(ε⁻¹√ν)^{-101/22} ε⁻² ≤ ν⁻³ ε^{57/22}` (`-101/22 + 2 = -57/22`, source 5203-5205, 5282-5289).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ag_add {a b G : ℝ≥0∞} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : a ≤ ENNReal.ofReal x * G) (hb : b ≤ ENNReal.ofReal y * G) :
    a + b ≤ ENNReal.ofReal (x + y) * G := by
  rw [ENNReal.ofReal_add hx hy, add_mul]
  exact add_le_add ha hb

theorem ag_smul {a G : ℝ≥0∞} {c x : ℝ} (hc : 0 ≤ c) (ha : a ≤ ENNReal.ofReal x * G) :
    ENNReal.ofReal c * a ≤ ENNReal.ofReal (c * x) * G := by
  rw [ENNReal.ofReal_mul hc, mul_assoc]
  exact mul_le_mul' le_rfl ha

theorem ag_coef {a G : ℝ≥0∞} {x x' : ℝ} (ha : a ≤ ENNReal.ofReal x * G) (hx : x ≤ x') :
    a ≤ ENNReal.ofReal x' * G :=
  ha.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hx) le_rfl)

theorem ag_unweight {κ : ℝ} (hκ : 0 < κ) {s G : ℝ≥0∞} (h : ENNReal.ofReal κ⁻¹ * s ≤ G) :
    s ≤ ENNReal.ofReal κ * G := by
  calc s = ENNReal.ofReal κ * (ENNReal.ofReal κ⁻¹ * s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hκ.le, mul_inv_cancel₀ hκ.ne', ENNReal.ofReal_one,
          one_mul]
    _ ≤ ENNReal.ofReal κ * G := mul_le_mul' le_rfl h

theorem ag_chain {a s G : ℝ≥0∞} {c κ : ℝ} (hc : 0 ≤ c) (ha : a ≤ ENNReal.ofReal c * s)
    (hs : s ≤ ENNReal.ofReal κ * G) : a ≤ ENNReal.ofReal (c * κ) * G := by
  rw [ENNReal.ofReal_mul hc, mul_assoc]
  exact ha.trans (mul_le_mul' le_rfl hs)

theorem ag_mem_streamAnn_merid (ν R : ℝ) (z : Space) :
    meridPt z ∈ streamAnn ν R ↔ z ∈ streamAnn ν R := by
  show (R * Real.sqrt ν ≤ ϱ (meridPt z) ∧ ϱ (meridPt z) ≤ R * Real.sqrt (5 * ν / 4)) ↔
    (R * Real.sqrt ν ≤ ϱ z ∧ ϱ z ≤ R * Real.sqrt (5 * ν / 4))
  rw [ag_meridPt_rho]

theorem ag_ann_merid (ν R : ℝ) (F : ℝ → ℝ≥0∞) (z : Space) :
    (streamAnn ν R).indicator (fun y => F (y 2)) (meridPt z) =
      (streamAnn ν R).indicator (fun y => F (y 2)) z := by
  by_cases h : z ∈ streamAnn ν R
  · rw [indicator_of_mem h, indicator_of_mem ((ag_mem_streamAnn_merid ν R z).2 h),
      ag_meridPt_two]
  · rw [indicator_of_notMem h,
      indicator_of_notMem (fun h' => h ((ag_mem_streamAnn_merid ν R z).1 h'))]

/-- `(c₀ L)^{x+y} = c₀^{x+y} L^x L^y`. -/
theorem ag_rpow_split {c₀ L : ℝ} (hc : 0 < c₀) (hL : 0 < L) (x y : ℝ) :
    (c₀ * L) ^ (x + y) = c₀ ^ (x + y) * (L ^ x * L ^ y) := by
  rw [Real.mul_rpow hc.le hL.le, Real.rpow_add hL]

/-- The physical rescaling (source 5203-5205, 5282-5289): `(ε⁻¹√ν)^{-101/22} ε⁻² ≤ ν⁻³ ε^{57/22}`. -/
theorem ag_scale_le {ν ε : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) :
    (ε⁻¹ * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) * (ε⁻¹) ^ 2 ≤ ν⁻¹ ^ 3 * ε ^ (57 / 22 : ℝ) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have e1 : (ε⁻¹) ^ (-(101 / 22 : ℝ)) = ε ^ (101 / 22 : ℝ) := by
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
  have e2 : Real.sqrt ν ^ (-(101 / 22 : ℝ)) = ν⁻¹ ^ (101 / 44 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hν.le, Real.inv_rpow hν.le, ← Real.rpow_neg hν.le]
    norm_num
  have hν' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have e3 : ν⁻¹ ^ (101 / 44 : ℝ) ≤ ν⁻¹ ^ 3 := by
    have := Real.rpow_le_rpow_of_exponent_le hν' (show (101 / 44 : ℝ) ≤ (3 : ℕ) by norm_num)
    rwa [Real.rpow_natCast] at this
  have e4 : ε ^ (101 / 22 : ℝ) * (ε⁻¹) ^ 2 = ε ^ (57 / 22 : ℝ) := by
    have h2 : (ε⁻¹) ^ 2 = ε ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hε.le, inv_pow]
      norm_cast
    rw [h2, ← Real.rpow_add hε]
    norm_num
  rw [Real.mul_rpow (inv_pos.2 hε).le hs.le, e1, e2]
  calc ε ^ (101 / 22 : ℝ) * ν⁻¹ ^ (101 / 44 : ℝ) * (ε⁻¹) ^ 2
      = ν⁻¹ ^ (101 / 44 : ℝ) * (ε ^ (101 / 22 : ℝ) * (ε⁻¹) ^ 2) := by ring
    _ = ν⁻¹ ^ (101 / 44 : ℝ) * ε ^ (57 / 22 : ℝ) := by rw [e4]
    _ ≤ ν⁻¹ ^ 3 * ε ^ (57 / 22 : ℝ) :=
        mul_le_mul_of_nonneg_right e3 (Real.rpow_nonneg hε.le _)


/-- The real coefficient identities of the assembly. -/
theorem ag_coef_real {Λ L w Cp C₁ C₂ Ch Cx0 Cx1 Cx2 Cw0 Cw1 Cψ : ℝ} (hΛ : 0 ≤ Λ) (hL : 0 < L)
    (hw : w = L⁻¹) (hCp : 0 ≤ Cp) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCh : 0 ≤ Ch) (hCx0 : 0 ≤ Cx0)
    (hCx1 : 0 ≤ Cx1) (hCx2 : 0 ≤ Cx2) (hCw0 : 0 ≤ Cw0) (hCw1 : 0 ≤ Cw1) (hCψ : 0 ≤ Cψ) :
    (Cw1 * Λ + C₁ * L ^ (-1 : ℝ) * (Cw0 * (Λ * L)) + C₁ * L ^ (-3 : ℝ) * (Cψ * (Λ * L ^ 3)) +
        C₂ * (w * (Cx0 * (Λ * L)) + Cx1 * Λ + w * (Cx2 * (Λ * w)) + w ^ 2 * (Cx1 * Λ) +
          w ^ 3 * (Cψ * (Λ * L ^ 3)))) +
      3 * (Cx1 * Λ + Cp * L ^ (-1 : ℝ) * (Cx0 * (Λ * L)) + Cp * L ^ (-3 : ℝ) * (Cψ * (Λ * L ^ 3))) +
      Ch * (Cx2 * (Λ * w) + w * (Cx1 * Λ) + w ^ 2 * (Cx0 * (Λ * L)) + w ^ 4 * (Cψ * (Λ * L ^ 3))) ≤
    Λ * (1 + w ^ 2) * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * ((Cx0 + Cx1 + Cψ) + (Cx2 + Cx1)) +
      3 * (Cx1 + Cp * Cx0 + Cp * Cψ) + Ch * (Cx2 + Cx1 + Cx0 + Cψ)) := by
  have hm1 : L ^ (-1 : ℝ) = w := by rw [Real.rpow_neg_one, hw]
  have hm3 : L ^ (-3 : ℝ) = w ^ 3 := by
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hL.le, Real.rpow_natCast,
      hw, inv_pow]
  have hwL : w * L = 1 := by rw [hw, inv_mul_cancel₀ hL.ne']
  have hw0 : 0 ≤ w := by rw [hw]; exact inv_nonneg.2 hL.le
  rw [hm1, hm3]
  have h3 : w ^ 3 * L ^ 3 = 1 := by rw [← mul_pow, hwL, one_pow]
  have h4 : w ^ 4 * L ^ 3 = w := by
    calc w ^ 4 * L ^ 3 = w * (w ^ 3 * L ^ 3) := by ring
      _ = w := by rw [h3, mul_one]
  have h2 : w ^ 2 * L = w := by
    calc w ^ 2 * L = w * (w * L) := by ring
      _ = w := by rw [hwL, mul_one]
  have key : (Cw1 * Λ + C₁ * w * (Cw0 * (Λ * L)) + C₁ * w ^ 3 * (Cψ * (Λ * L ^ 3)) +
        C₂ * (w * (Cx0 * (Λ * L)) + Cx1 * Λ + w * (Cx2 * (Λ * w)) + w ^ 2 * (Cx1 * Λ) +
          w ^ 3 * (Cψ * (Λ * L ^ 3)))) +
      3 * (Cx1 * Λ + Cp * w * (Cx0 * (Λ * L)) + Cp * w ^ 3 * (Cψ * (Λ * L ^ 3))) +
      Ch * (Cx2 * (Λ * w) + w * (Cx1 * Λ) + w ^ 2 * (Cx0 * (Λ * L)) + w ^ 4 * (Cψ * (Λ * L ^ 3))) =
      Λ * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * (Cx0 + Cx1 + Cψ) + 3 * (Cx1 + Cp * Cx0 + Cp * Cψ)) +
        Λ * w * (Ch * (Cx2 + Cx1 + Cx0 + Cψ)) + Λ * w ^ 2 * (C₂ * (Cx2 + Cx1)) := by
    linear_combination (C₁ * Cw0 * Λ + C₂ * Cx0 * Λ + 3 * Cp * Cx0 * Λ) * hwL +
      (C₁ * Cψ * Λ + C₂ * Cψ * Λ + 3 * Cp * Cψ * Λ) * h3 + (Ch * Cx0 * Λ) * h2 +
      (Ch * Cψ * Λ) * h4
  rw [key]
  have hA : 0 ≤ (Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * (Cx0 + Cx1 + Cψ) + 3 * (Cx1 + Cp * Cx0 + Cp * Cψ) :=
    by positivity
  have hB : 0 ≤ Ch * (Cx2 + Cx1 + Cx0 + Cψ) := by positivity
  have hC : 0 ≤ C₂ * (Cx2 + Cx1) := by positivity
  have hw1 : w ≤ 1 + w ^ 2 := by nlinarith [sq_nonneg (w - 1)]
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  have e1 : Λ * w * (Ch * (Cx2 + Cx1 + Cx0 + Cψ)) ≤ Λ * (1 + w ^ 2) * (Ch * (Cx2 + Cx1 + Cx0 + Cψ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw1 hΛ) hB
  have e0 : Λ * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * (Cx0 + Cx1 + Cψ) + 3 * (Cx1 + Cp * Cx0 + Cp * Cψ)) ≤
      Λ * (1 + w ^ 2) * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * (Cx0 + Cx1 + Cψ) +
        3 * (Cx1 + Cp * Cx0 + Cp * Cψ)) := by
    have : Λ ≤ Λ * (1 + w ^ 2) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hA
  have e2 : Λ * w ^ 2 * (C₂ * (Cx2 + Cx1)) ≤ Λ * (1 + w ^ 2) * (C₂ * (Cx2 + Cx1)) := by
    have : Λ * w ^ 2 ≤ Λ * (1 + w ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hΛ
    exact mul_le_mul_of_nonneg_right this hC
  calc Λ * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * (Cx0 + Cx1 + Cψ) + 3 * (Cx1 + Cp * Cx0 + Cp * Cψ)) +
        Λ * w * (Ch * (Cx2 + Cx1 + Cx0 + Cψ)) + Λ * w ^ 2 * (C₂ * (Cx2 + Cx1))
      ≤ Λ * (1 + w ^ 2) * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) + C₂ * (Cx0 + Cx1 + Cψ) +
          3 * (Cx1 + Cp * Cx0 + Cp * Cψ)) + Λ * (1 + w ^ 2) * (Ch * (Cx2 + Cx1 + Cx0 + Cψ)) +
          Λ * (1 + w ^ 2) * (C₂ * (Cx2 + Cx1)) := by linarith
    _ = _ := by ring

/-- **The `ℝ≥0∞` assembly of the jet density** (source 5203-5217, 5267-5268): the leaves of
`DX`, `DY` and `D²X` with the unit majorant bounds give one majorant `G`. -/
theorem ag_core {Λ L Cp C₁ C₂ Ch Cx0 Cx1 Cx2 Cw0 Cw1 Cψ : ℝ} (hΛ : 0 ≤ Λ) (hL : 0 < L)
    (hCp : 0 ≤ Cp) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCh : 0 ≤ Ch) (hCx0 : 0 ≤ Cx0)
    (hCx1 : 0 ≤ Cx1) (hCx2 : 0 ≤ Cx2) (hCw0 : 0 ≤ Cw0) (hCw1 : 0 ≤ Cw1) (hCψ : 0 ≤ Cψ)
    {G jx0 jx1 jx2 jw0 jw1 px pw pz dX dY dH : ℝ≥0∞}
    (hjx0 : jx0 ≤ ENNReal.ofReal (Cx0 * (Λ * L)) * G) (hjx1 : jx1 ≤ ENNReal.ofReal (Cx1 * Λ) * G)
    (hjx2 : jx2 ≤ ENNReal.ofReal (Cx2 * (Λ * L⁻¹)) * G)
    (hjw0 : jw0 ≤ ENNReal.ofReal (Cw0 * (Λ * L)) * G) (hjw1 : jw1 ≤ ENNReal.ofReal (Cw1 * Λ) * G)
    (hpx : px ≤ ENNReal.ofReal (Cψ * (Λ * L ^ 3)) * G)
    (hpw : pw ≤ ENNReal.ofReal (Cψ * (Λ * L ^ 3)) * G)
    (hpz : pz ≤ ENNReal.ofReal (Cψ * (Λ * L ^ 3)) * G)
    (hdX : dX ≤ jx1 + ENNReal.ofReal (Cp * L ^ (-1 : ℝ)) * jx0 +
      ENNReal.ofReal (Cp * L ^ (-3 : ℝ)) * px)
    (hdY : dY ≤ (jw1 + ENNReal.ofReal (C₁ * L ^ (-1 : ℝ)) * jw0 +
        ENNReal.ofReal (C₁ * L ^ (-3 : ℝ)) * pw) +
      ENNReal.ofReal C₂ * (ENNReal.ofReal L⁻¹ * jx0 + jx1 + ENNReal.ofReal L⁻¹ * jx2 +
        ENNReal.ofReal (L⁻¹ ^ 2) * jx1 + ENNReal.ofReal (L⁻¹ ^ 3) * px))
    (hdH : dH ≤ ENNReal.ofReal Ch * (jx2 + ENNReal.ofReal L⁻¹ * jx1 +
      ENNReal.ofReal (L⁻¹ ^ 2) * jx0 + ENNReal.ofReal (L⁻¹ ^ 4) * pz)) :
    dY + ENNReal.ofReal 3 * dX + dH ≤
      ENNReal.ofReal (Λ * (1 + L⁻¹ ^ 2) * ((Cw1 + C₁ * Cw0 + C₁ * Cψ) +
        C₂ * ((Cx0 + Cx1 + Cψ) + (Cx2 + Cx1)) + 3 * (Cx1 + Cp * Cx0 + Cp * Cψ) +
        Ch * (Cx2 + Cx1 + Cx0 + Cψ))) * G := by
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hm1 : 0 ≤ L ^ (-1 : ℝ) := Real.rpow_nonneg hL.le _
  have hm3 : 0 ≤ L ^ (-3 : ℝ) := Real.rpow_nonneg hL.le _
  have hX := hdX.trans (ag_add (by positivity) (by positivity)
    (ag_add (by positivity) (by positivity) hjx1 (ag_smul (by positivity) hjx0))
    (ag_smul (by positivity) hpx))
  have hY := hdY.trans (ag_add (by positivity) (by positivity)
    (ag_add (by positivity) (by positivity)
      (ag_add (by positivity) (by positivity) hjw1 (ag_smul (by positivity) hjw0))
      (ag_smul (by positivity) hpw))
    (ag_smul hC₂ (ag_add (by positivity) (by positivity)
      (ag_add (by positivity) (by positivity)
        (ag_add (by positivity) (by positivity)
          (ag_add (by positivity) (by positivity) (ag_smul hLi hjx0) hjx1)
          (ag_smul hLi hjx2))
        (ag_smul (by positivity) hjx1))
      (ag_smul (by positivity) hpx))))
  have hH := hdH.trans (ag_smul hCh (ag_add (by positivity) (by positivity)
    (ag_add (by positivity) (by positivity)
      (ag_add (by positivity) (by positivity) hjx2 (ag_smul hLi hjx1))
      (ag_smul (by positivity) hjx0))
    (ag_smul (by positivity) hpz)))
  have hT := ag_add (by positivity) (by positivity)
    (ag_add (by positivity) (by positivity) hY (ag_smul (c := 3) (by norm_num) hX)) hH
  exact ag_coef hT (ag_coef_real hΛ hL rfl hCp hC₁ hC₂ hCh hCx0 hCx1 hCx2 hCw0 hCw1 hCψ)

end UnforcedLeray.Short.PartIIIb.Concrete

end
