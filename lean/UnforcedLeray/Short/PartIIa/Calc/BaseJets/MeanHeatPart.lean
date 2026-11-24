import UnforcedLeray.Short.PartIIa.Calc.BaseJets

/-!
# Part II-a, task `PartII-a:R02/8/19`: mean heat part

Source of record: `the November 2 reference manuscript`, lines 447-459
(`|a_{2j}| ≤ P`, `sct:expansion`) and lines 1267-1272 (heat size). The word `a₀ (-(b+1))^ℓ ∂_η^b G`
has size `(νs)^{-(b+1)/2}`, which for `ν ≤ 1`, `s ≥ 1` is `ν^{-(b+1)/2} s^{-(b+1)/2}`, and
`ν^{-(b+1)/2} ≤ (1 + c + ν⁻¹)^{b+1}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanCoeff)

theorem meanHeatPart_of (h : LateIngredients) : MeanHeatPart := by
  intro ℓ b ρ m hρ
  obtain ⟨Ca, Na, νa, hνa, Ha⟩ := h.coeff ρ 0 hρ
  obtain ⟨Ch, hCh, Hh⟩ := h.heat.2.1 m b
  refine ⟨max Ca 0 * ((b : ℝ) + 1) ^ ℓ * Ch, Na + (b + 1), min νa 1, lt_min hνa one_pos,
    fun ν hν hνle tr htr x hx => ?_⟩
  dsimp only
  rw [show (1 / 2 + (b : ℝ) / 2) = ((b : ℝ) + 1) / 2 by ring]
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνa' : ν ≤ νa := hνle.trans (min_le_left _ _)
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hinv : 0 < ν⁻¹ := inv_pos.2 hν
  have hs1 : 1 ≤ x.2.2 := hx
  have hs0 : 0 < x.2.2 := by linarith
  have hA' : |meanCoeff tr 0| ≤ polyConst (max Ca 0) Na ν (ν ^ (-ρ)) :=
    (Ha ν hν hνa' tr htr).trans (polyConst_mono hν hc (le_max_left Ca 0) (le_max_right Ca 0) le_rfl)
  have hA0 : 0 ≤ polyConst (max Ca 0) Na ν (ν ^ (-ρ)) := (abs_nonneg _).trans hA'
  have hB : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[b] (heatProfile ν)) x| ≤
      Ch * (ν * x.2.2) ^ (-(((b : ℝ) + 1) / 2)) :=
    Hh ν hν hν1 x hs1
  have hsplit : (ν * x.2.2) ^ (-(((b : ℝ) + 1) / 2)) =
      ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2)) :=
    Real.mul_rpow hν.le hs0.le
  have hi1 : (1 : ℝ) ≤ ν⁻¹ := by nlinarith [mul_inv_cancel₀ hν.ne']
  have hnu : ν ^ (-(((b : ℝ) + 1) / 2)) ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ (b + 1) := by
    have e1 : ν ^ (-(((b : ℝ) + 1) / 2)) = ν⁻¹ ^ (((b : ℝ) + 1) / 2) := by
      rw [Real.rpow_neg hν.le, Real.inv_rpow hν.le]
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have e2 : ν⁻¹ ^ (((b : ℝ) + 1) / 2) ≤ ν⁻¹ ^ ((b : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)
    have e3 : ν⁻¹ ^ ((b : ℝ) + 1) = ν⁻¹ ^ (b + 1) := by
      rw [← Real.rpow_natCast]; norm_cast
    have e4 : ν⁻¹ ^ (b + 1) ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ (b + 1) :=
      pow_le_pow_left₀ hinv.le (by linarith) _
    rw [e1]; linarith
  have hP : (0 : ℝ) ≤ ((b : ℝ) + 1) ^ ℓ := by positivity
  have hW : (1 + x.2.1 ^ 2 / x.2.2) ^ m *
      |meanCoeff tr 0 * ((-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) x)| =
      |meanCoeff tr 0| * ((b : ℝ) + 1) ^ ℓ *
        ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[b] (heatProfile ν)) x|) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) + 1)]
    ring
  have hWB : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[b] (heatProfile ν)) x| ≤
      Ch * (ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2))) := by
    rw [← hsplit]; exact hB
  have hmain : |meanCoeff tr 0| * ((b : ℝ) + 1) ^ ℓ *
      ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[b] (heatProfile ν)) x|) ≤
      polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((b : ℝ) + 1) ^ ℓ *
        (Ch * (ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2)))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA' hP) hWB
      (mul_nonneg (weight_nonneg m hs1) (abs_nonneg _)) (mul_nonneg hA0 hP)
  have hfin : polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((b : ℝ) + 1) ^ ℓ *
      (Ch * (ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2)))) ≤
      polyConst (max Ca 0 * ((b : ℝ) + 1) ^ ℓ * Ch) (Na + (b + 1)) ν (ν ^ (-ρ)) *
        x.2.2 ^ (-(((b : ℝ) + 1) / 2)) := by
    have hm : ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2)) ≤
        (1 + ν ^ (-ρ) + ν⁻¹) ^ (b + 1) * x.2.2 ^ (-(((b : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_right hnu (Real.rpow_nonneg hs0.le _)
    have h2 : Ch * (ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2))) ≤
        Ch * ((1 + ν ^ (-ρ) + ν⁻¹) ^ (b + 1) * x.2.2 ^ (-(((b : ℝ) + 1) / 2))) :=
      mul_le_mul_of_nonneg_left hm hCh
    calc polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((b : ℝ) + 1) ^ ℓ *
          (Ch * (ν ^ (-(((b : ℝ) + 1) / 2)) * x.2.2 ^ (-(((b : ℝ) + 1) / 2))))
        ≤ polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((b : ℝ) + 1) ^ ℓ *
          (Ch * ((1 + ν ^ (-ρ) + ν⁻¹) ^ (b + 1) * x.2.2 ^ (-(((b : ℝ) + 1) / 2)))) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hA0 hP)
      _ = polyConst (max Ca 0 * ((b : ℝ) + 1) ^ ℓ * Ch) (Na + (b + 1)) ν (ν ^ (-ρ)) *
          x.2.2 ^ (-(((b : ℝ) + 1) / 2)) := by
          unfold polyConst; ring
  exact hW.trans_le (hmain.trans hfin)

end UnforcedLeray.Short.PartIIa.Jet
