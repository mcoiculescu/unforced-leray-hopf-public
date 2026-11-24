import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg

/-!
# `PartIII-b:C/rep/5/2/2/5` : the pointwise size of the stream correction on the annulus

Source `the November 2 reference manuscript` 4180-4186 (`C_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z`),
3684-3692 (`χ'/ρ = O(D^{-2})`). Pure calculus: `streamCorr = (χ̂'(t)·(-2νR²/ϱ³)/ϱ·Ψ_Z) e_z` with
`t = ν·age R y = νR²/ϱ²`. On the annulus `4/5 ≤ t ≤ 1` the derivative `χ̂'` is bounded (continuous
and supported in `[4/5,1]`), and `2νR²/ϱ⁴ ≤ 2/(R²ν)` there since `ϱ ≥ R√ν`. Off the annulus
`t > 1` or `t < 4/5`, where `χ̂' = 0`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcp_deriv_of_lt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : t < 4 / 5) :
    deriv χ t = 0 := by
  have hev : χ =ᶠ[nhds t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with u hu using hχ.one u (le_of_lt hu)
  rw [hev.deriv_eq]
  simp

theorem tcp_deriv_of_gt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : 1 < t) :
    deriv χ t = 0 := by
  have hev : χ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu using hχ.zero u (le_of_lt hu)
  rw [hev.deriv_eq]
  simp

/-- `t = νR²/s²` lies in `[4/5, 1]` on the annulus `R√ν ≤ s ≤ R√(5ν/4)`. -/
theorem tcp_t_bounds (ν R s : ℝ) (hν : 0 < ν) (hR : 0 < R) (hs : 0 < s)
    (h1 : R * Real.sqrt ν ≤ s) (h2 : s ≤ R * Real.sqrt (5 * ν / 4)) :
    4 / 5 ≤ ν * (R ^ 2 / s ^ 2) ∧ ν * (R ^ 2 / s ^ 2) ≤ 1 := by
  have ea : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by
    rw [mul_pow, Real.sq_sqrt hν.le]
  have eb : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hA : R ^ 2 * ν ≤ s ^ 2 := by
    rw [← ea]; exact pow_le_pow_left₀ (by positivity) h1 2
  have hB : s ^ 2 ≤ R ^ 2 * (5 * ν / 4) := by
    rw [← eb]; exact pow_le_pow_left₀ hs.le h2 2
  have e : ν * (R ^ 2 / s ^ 2) = ν * R ^ 2 / s ^ 2 := by ring
  rw [e]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_one (by positivity)]
    nlinarith

/-- The key size bound `2νR²/s⁴ ≤ 2/(R²ν)` for `s ≥ R√ν`. -/
theorem tcp_size (ν R s : ℝ) (hν : 0 < ν) (hR : 0 < R) (hs : 0 < s)
    (h1 : R * Real.sqrt ν ≤ s) : 2 * ν * R ^ 2 / s ^ 4 ≤ 2 / (R ^ 2 * ν) := by
  have hw : 0 < R ^ 2 * ν := by positivity
  have hX : R ^ 2 * ν ≤ s ^ 2 := by
    have ea : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by
      rw [mul_pow, Real.sq_sqrt hν.le]
    rw [← ea]; exact pow_le_pow_left₀ (by positivity) h1 2
  rw [div_le_div_iff₀ (by positivity) hw]
  have hm := mul_le_mul hX hX hw.le (by positivity)
  nlinarith [hm]

/-- **`TransCutPoint`** (source 4180-4186, 3684-3692). -/
theorem transCutPoint : TransCutPoint := by
  intro χy hχ
  have hcont : Continuous (deriv χy) := hχ.smooth.continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (4 / 5 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨2 * |M|, by positivity, ?_⟩
  intro ν R hν hR Z τ y hy
  unfold streamCorr
  have hcv : ‖coordinateVector (2 : Fin 3)‖ₑ = 1 := by
    rw [← ofReal_norm_eq_enorm]
    have : ‖coordinateVector (2 : Fin 3)‖ = 1 := by
      simp [coordinateVector, EuclideanSpace.norm_single]
    rw [this, ENNReal.ofReal_one]
  rw [enorm_smul, hcv, mul_one, Real.enorm_eq_ofReal_abs]
  by_cases hA : y ∈ streamAnn ν R
  · rw [Set.indicator_of_mem hA]
    obtain ⟨h1, h2⟩ := hA
    obtain ⟨ht1, ht2⟩ := tcp_t_bounds ν R (ϱ y) hν hR hy h1 h2
    have hd : |deriv χy (ν * age R y)| ≤ |M| := by
      have := hM (ν * age R y) ⟨ht1, ht2⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self M)
    have hq : |(deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
        outPrim Z τ (ϱ y) (y 2))| ≤
        |M| * (2 / (R ^ 2 * ν)) * |outPrim Z τ (ϱ y) (y 2)| := by
      have hage : age R y = R ^ 2 / ϱ y ^ 2 := rfl
      have hsz := tcp_size ν R (ϱ y) hν hR hy h1
      have hK : deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y =
          -(deriv χy (ν * age R y) * (2 * ν * R ^ 2 / ϱ y ^ 4)) := by
        ring
      rw [hK, abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ν * R ^ 2 / ϱ y ^ 4)]
      have hpos : 0 ≤ 2 * ν * R ^ 2 / ϱ y ^ 4 := by positivity
      have h3 : |deriv χy (ν * age R y)| * (2 * ν * R ^ 2 / ϱ y ^ 4) ≤ |M| * (2 / (R ^ 2 * ν)) :=
        mul_le_mul hd hsz hpos (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    have hT : (transLen ν R)⁻¹ ^ 2 = (R ^ 2 * ν)⁻¹ := by
      unfold transLen
      have ea : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by
        rw [mul_pow, Real.sq_sqrt hν.le]
      rw [inv_pow, ea]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have e2 : 2 * (R ^ 2 * ν)⁻¹ = 2 / (R ^ 2 * ν) := by ring
    calc _ ≤ |M| * (2 / (R ^ 2 * ν)) * |outPrim Z τ (ϱ y) (y 2)| := hq
      _ = 2 * |M| * (transLen ν R)⁻¹ ^ 2 * |outPrim Z τ (ϱ y) (y 2)| := by
        rw [hT]; rw [← e2]; ring
  · rw [Set.indicator_of_notMem hA]
    have ea : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by
      rw [mul_pow, Real.sq_sqrt hν.le]
    have eb : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hp : 0 < ϱ y ^ 2 := by positivity
    have hcase : ν * age R y < 4 / 5 ∨ 1 < ν * age R y := by
      have e : ν * age R y = ν * R ^ 2 / ϱ y ^ 2 := by unfold age; ring
      rw [e]
      by_cases hle : R * Real.sqrt ν ≤ ϱ y
      · left
        have hb : R * Real.sqrt (5 * ν / 4) < ϱ y := by
          by_contra hh
          push_neg at hh
          exact hA ⟨hle, hh⟩
        have hsq : (R * Real.sqrt (5 * ν / 4)) ^ 2 < ϱ y ^ 2 :=
          pow_lt_pow_left₀ hb (by positivity) (by norm_num)
        rw [eb] at hsq
        rw [div_lt_iff₀ hp]
        nlinarith
      · right
        push_neg at hle
        have hsq : ϱ y ^ 2 < (R * Real.sqrt ν) ^ 2 :=
          pow_lt_pow_left₀ hle hy.le (by norm_num)
        rw [ea] at hsq
        rw [lt_div_iff₀ hp]
        nlinarith
    rcases hcase with hlt | hgt
    · simp [tcp_deriv_of_lt hχ hlt]
    · simp [tcp_deriv_of_gt hχ hgt]

end UnforcedLeray.Short.PartIIIb.Concrete
