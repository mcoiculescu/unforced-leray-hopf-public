import UnforcedLeray.Short.PartIIIa.Targets

/-!
# T13: the thin global bound from `sep:young` and Minkowski (SP 3670-3680)

Proves `UnforcedLeray.Short.IIIa.ThinGlobalOfParts` (statement in `Targets.lean`): `SepThinGlobal`
follows from `SepYoung` and `LtauMinkowski`.

Proof. Apply `SepYoung` with `p = 1` and `b = q` (so `1 + 1/q = 1/1 + 1/q`) and `δ = 5/2`, which is
admissible because `2 Re μ + 3 > 5/2` on `K` (`Re μ > -1/4`). This gives `C₀` with
`‖1_young D^jW_μ‖_{L²_τL^q} ≤ C₀ D^e ‖T‖_{L²_τL¹}`, where `D = r_i - r_o` and `e = -4-j+3/q < 0`.
`LtauMinkowski` and the thin-source hypothesis give `‖T‖_{L²_τL¹} ≤ R²N₀`. Since `D ≥ c₀R√ν > 0`
and `e < 0`, `D^e ≤ (c₀R√ν)^e = c₀^e R^e ν^{e/2}`. For `0 < ν ≤ 1` and `k = j + 4`,
`ν^{e/2} ≤ (ν⁻¹)^k` because `e/2 ≥ -k`. The constant is `C = C₀ c₀^e`, and `R^e R² = R^{-2-j+3/q}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **T13** (`thinGlobal_of_parts`, SP 3670-3680): `SepThinGlobal` from `SepYoung` and
Minkowski's inequality `LtauMinkowski`. -/
theorem thinGlobal_of_parts : UnforcedLeray.Short.IIIa.ThinGlobalOfParts := by
  intro hY hM K hK hKre j q c₀ hq hc₀
  obtain ⟨C₀, hC₀, hYb⟩ := hY K hK hKre j 1 q q (by norm_num) hq.le hq.le (by norm_num)
    ⟨5 / 2, by norm_num, fun μ hμ => by have := hKre μ hμ; linarith⟩
  refine ⟨C₀ * c₀ ^ (-4 - (j : ℝ) + 3 / q), j + 4,
    mul_nonneg hC₀ (Real.rpow_nonneg hc₀.le _), ?_⟩
  intro ν hν hν1 μ hμ R N₀ rOut rIn P hR hN₀ hrOut hrr hP hgap T hT hthin
  have hR0 : 0 < R := by linarith
  have hpos : 0 < c₀ * R * Real.sqrt ν := mul_pos (mul_pos hc₀ hR0) (Real.sqrt_pos.2 hν)
  have hD : 0 < rIn - rOut := lt_of_lt_of_le hpos hgap
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hq0 : 0 < q := by linarith
  set e : ℝ := -4 - (j : ℝ) + 3 / q with he
  have h3q : 3 / q < 3 := by
    rw [div_lt_iff₀ hq0]
    linarith
  have h3q0 : 0 < 3 / q := div_pos (by norm_num) hq0
  have he0 : e < 0 := by linarith
  -- The thin-source bound on the `L²_τL¹` norm (Minkowski).
  have hMink : ltauLq P 1 (srcNorm T) ≤ ENNReal.ofReal (R ^ 2 * N₀) :=
    (hM P hP T hT.measurable).trans hthin
  have hA : 0 ≤ C₀ * (rIn - rOut) ^ e := mul_nonneg hC₀ (Real.rpow_nonneg hD.le _)
  -- The young bound, combined with the thin-source bound.
  have hCombine : ltauLq P q (youngDerivNorm ν μ T j rIn) ≤
      ENNReal.ofReal (C₀ * (rIn - rOut) ^ e) * ENNReal.ofReal (R ^ 2 * N₀) := by
    refine (hYb ν hν μ hμ rOut rIn P hrOut hrr hP T hT).trans ?_
    gcongr
  -- The gap bound `D^e ≤ (c₀R√ν)^e = c₀^e R^e ν^{e/2}`.
  have hPos : 0 ≤ c₀ ^ e * R ^ e :=
    mul_nonneg (Real.rpow_nonneg hc₀.le _) (Real.rpow_nonneg hR0.le _)
  have h1 : (rIn - rOut) ^ e ≤ (c₀ * R * Real.sqrt ν) ^ e :=
    Real.rpow_le_rpow_of_nonpos hpos hgap he0.le
  have h2 : (c₀ * R * Real.sqrt ν) ^ e = c₀ ^ e * R ^ e * ν ^ ((1 / 2 : ℝ) * e) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (mul_nonneg hc₀.le hR0.le)
        (Real.rpow_nonneg hν.le (1 / 2 : ℝ)), Real.mul_rpow hc₀.le hR0.le,
      ← Real.rpow_mul hν.le]
  -- `ν^{e/2} ≤ (ν⁻¹)^k` for `0 < ν ≤ 1`, `k = j + 4`, since `e/2 ≥ -k`.
  have hexp : -((j + 4 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * e := by
    push_cast
    linarith
  have hνk : ν ^ ((1 / 2 : ℝ) * e) ≤ (ν⁻¹) ^ (j + 4) := by
    rw [inv_pow]
    have h := Real.rpow_le_rpow_of_exponent_ge hν hν1 hexp
    rwa [Real.rpow_neg hν.le, Real.rpow_natCast] at h
  have hstep : (rIn - rOut) ^ e ≤ c₀ ^ e * R ^ e * (ν⁻¹) ^ (j + 4) := by
    calc (rIn - rOut) ^ e ≤ (c₀ * R * Real.sqrt ν) ^ e := h1
      _ = c₀ ^ e * R ^ e * ν ^ ((1 / 2 : ℝ) * e) := h2
      _ ≤ c₀ ^ e * R ^ e * (ν⁻¹) ^ (j + 4) := mul_le_mul_of_nonneg_left hνk hPos
  have h4 : C₀ * (rIn - rOut) ^ e ≤ C₀ * (c₀ ^ e * R ^ e * (ν⁻¹) ^ (j + 4)) :=
    mul_le_mul_of_nonneg_left hstep hC₀
  -- `R^e R² = R^{e+2}` with `e + 2 = -2 - j + 3/q`.
  have hRe : R ^ (-2 - (j : ℝ) + 3 / q) = R ^ e * R ^ 2 := by
    have hsh : (-2 - (j : ℝ) + 3 / q) = e + 2 := by
      rw [he]
      ring
    rw [hsh, Real.rpow_add hR0, Real.rpow_two]
  have hreal : C₀ * (rIn - rOut) ^ e * (R ^ 2 * N₀) ≤
      C₀ * c₀ ^ e * (ν⁻¹) ^ (j + 4) * R ^ (-2 - (j : ℝ) + 3 / q) * N₀ := by
    calc C₀ * (rIn - rOut) ^ e * (R ^ 2 * N₀)
        ≤ C₀ * (c₀ ^ e * R ^ e * (ν⁻¹) ^ (j + 4)) * (R ^ 2 * N₀) :=
          mul_le_mul_of_nonneg_right h4 (mul_nonneg (sq_nonneg R) hN₀)
      _ = C₀ * c₀ ^ e * (ν⁻¹) ^ (j + 4) * R ^ (-2 - (j : ℝ) + 3 / q) * N₀ := by
          rw [hRe]
          ring
  have hfinal : ltauLq P q (youngDerivNorm ν μ T j rIn) ≤
      ENNReal.ofReal (C₀ * c₀ ^ e * (ν⁻¹) ^ (j + 4) * R ^ (-2 - (j : ℝ) + 3 / q) * N₀) := by
    calc ltauLq P q (youngDerivNorm ν μ T j rIn)
        ≤ ENNReal.ofReal (C₀ * (rIn - rOut) ^ e) * ENNReal.ofReal (R ^ 2 * N₀) := hCombine
      _ = ENNReal.ofReal (C₀ * (rIn - rOut) ^ e * (R ^ 2 * N₀)) :=
          (ENNReal.ofReal_mul hA).symm
      _ ≤ ENNReal.ofReal (C₀ * c₀ ^ e * (ν⁻¹) ^ (j + 4) * R ^ (-2 - (j : ℝ) + 3 / q) * N₀) :=
          ENNReal.ofReal_le_ofReal hreal
  exact hfinal

end UnforcedLeray.Short.IIIa
