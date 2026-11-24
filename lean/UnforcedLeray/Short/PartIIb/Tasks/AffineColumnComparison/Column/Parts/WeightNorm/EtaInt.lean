import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# The `η`-integral of a polynomial times a decaying exponential (helper of `ColWeightNorm`)

Source: `the November 2 reference manuscript` line 2385.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.WeightNormAux

/-- `∫_ℝ e^{-a|η|} dη ≤ 2/a`. -/
theorem lintegral_exp_neg_abs_le {a : ℝ} (ha : 0 < a) :
    ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-(a * |η|))) ≤ ENNReal.ofReal (2 / a) := by
  have hu : (univ : Set ℝ) = Iic 0 ∪ Ioi 0 := (Set.Iic_union_Ioi).symm
  have h1 : ∫⁻ η in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(a * |η|))) = ENNReal.ofReal (1 / a) := by
    have e : ∫⁻ η in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(a * |η|))) =
        ∫⁻ η in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp ((-a) * η)) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun η hη => ?_)
      have : |η| = η := abs_of_pos hη
      rw [this]; congr 2; ring
    rw [e, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (by linarith) 0)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_Ioi (by linarith) 0]
    congr 1; simp
  have h2 : ∫⁻ η in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (-(a * |η|))) = ENNReal.ofReal (1 / a) := by
    have e : ∫⁻ η in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (-(a * |η|))) =
        ∫⁻ η in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (a * η)) := by
      refine setLIntegral_congr_fun measurableSet_Iic (fun η hη => ?_)
      have : |η| = -η := abs_of_nonpos hη
      rw [this]; congr 2; ring
    rw [e, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha 0)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_Iic ha 0]
    simp
  calc ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-(a * |η|)))
      = ∫⁻ η in (univ : Set ℝ), ENNReal.ofReal (Real.exp (-(a * |η|))) := by
        rw [Measure.restrict_univ]
    _ ≤ (∫⁻ η in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (-(a * |η|)))) +
        ∫⁻ η in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(a * |η|))) := by
        rw [hu]; exact lintegral_union_le _ _ _
    _ = ENNReal.ofReal (2 / a) := by
        rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- `(1+u)^m e^{-bu} ≤ K e^{-bu/2}` for `u ≥ 0`. -/
theorem poly_exp_le {m b : ℝ} (hm : 0 ≤ m) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ m * Real.exp (-(b * u)) ≤ K * Real.exp (-((b / 2) * u)) := by
  set n : ℕ := ⌈m⌉₊ with hn
  refine ⟨(n.factorial : ℝ) * (2 / b) ^ n * Real.exp (b / 2), by positivity, fun u hu => ?_⟩
  have h1 : (1 + u) ^ m ≤ (1 + u) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil m)
  rw [Real.rpow_natCast] at h1
  have h2 := Real.pow_div_factorial_le_exp (x := (b / 2) * (1 + u)) (by positivity) n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have h3 : (1 + u) ^ n ≤ (n.factorial : ℝ) * (2 / b) ^ n * Real.exp ((b / 2) * (1 + u)) := by
    rw [div_le_iff₀ hfac, mul_pow] at h2
    have : (2 / b) ^ n * (b / 2) ^ n = 1 := by
      rw [← mul_pow, show 2 / b * (b / 2) = 1 by field_simp, one_pow]
    calc (1 + u) ^ n = (2 / b) ^ n * (b / 2) ^ n * (1 + u) ^ n := by rw [this, one_mul]
      _ = (2 / b) ^ n * ((b / 2) ^ n * (1 + u) ^ n) := by ring
      _ ≤ (2 / b) ^ n * (Real.exp ((b / 2) * (1 + u)) * n.factorial) := by gcongr
      _ = _ := by ring
  calc (1 + u) ^ m * Real.exp (-(b * u))
      ≤ ((n.factorial : ℝ) * (2 / b) ^ n * Real.exp ((b / 2) * (1 + u))) * Real.exp (-(b * u)) := by
        gcongr; exact h1.trans h3
    _ = (n.factorial : ℝ) * (2 / b) ^ n * Real.exp (b / 2) * Real.exp (-((b / 2) * u)) := by
        rw [mul_assoc _ (Real.exp _) , ← Real.exp_add, mul_assoc _ _ (Real.exp (-((b / 2) * u))),
          ← Real.exp_add]
        congr 2; ring

/-- **The `η`-integral** (SP 2385): for `c ≥ 1`,
`∫_ℝ (1+|η|)^m e^{-b|η|/c} dη ≤ K' c^{m+1}`. -/
theorem lintegral_eta_le {m b : ℝ} (hm : 0 ≤ m) (hb : 0 < b) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ c : ℝ, 1 ≤ c →
      ∫⁻ η : ℝ, ENNReal.ofReal ((1 + |η|) ^ m * Real.exp (-(b * |η| / c))) ≤
        ENNReal.ofReal (K' * c ^ (m + 1)) := by
  obtain ⟨K, hK, hKb⟩ := poly_exp_le hm hb
  refine ⟨4 * K / b, by positivity, fun c hc => ?_⟩
  have hc0 : 0 < c := by linarith
  have hpt : ∀ η : ℝ, ENNReal.ofReal ((1 + |η|) ^ m * Real.exp (-(b * |η| / c))) ≤
      ENNReal.ofReal (c ^ m * K) * ENNReal.ofReal (Real.exp (-((b / (2 * c)) * |η|))) := by
    intro η
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hu : 0 ≤ |η| / c := by positivity
    have e1 : 1 + |η| ≤ c * (1 + |η| / c) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hc0.ne']; linarith
    have e2 : (1 + |η|) ^ m ≤ c ^ m * (1 + |η| / c) ^ m := by
      calc (1 + |η|) ^ m ≤ (c * (1 + |η| / c)) ^ m :=
            Real.rpow_le_rpow (by positivity) e1 hm
        _ = _ := Real.mul_rpow hc0.le (by positivity)
    have e3 := hKb (|η| / c) hu
    have e4 : -(b * (|η| / c)) = -(b * |η| / c) := by ring
    have e5 : -((b / 2) * (|η| / c)) = -((b / (2 * c)) * |η|) := by field_simp
    rw [e4, e5] at e3
    calc (1 + |η|) ^ m * Real.exp (-(b * |η| / c))
        ≤ (c ^ m * (1 + |η| / c) ^ m) * Real.exp (-(b * |η| / c)) := by gcongr
      _ = c ^ m * ((1 + |η| / c) ^ m * Real.exp (-(b * |η| / c))) := by ring
      _ ≤ c ^ m * (K * Real.exp (-((b / (2 * c)) * |η|))) := by gcongr
      _ = _ := by ring
  have ha : 0 < b / (2 * c) := by positivity
  calc ∫⁻ η : ℝ, ENNReal.ofReal ((1 + |η|) ^ m * Real.exp (-(b * |η| / c)))
      ≤ ∫⁻ η : ℝ, ENNReal.ofReal (c ^ m * K) *
          ENNReal.ofReal (Real.exp (-((b / (2 * c)) * |η|))) := lintegral_mono hpt
    _ = ENNReal.ofReal (c ^ m * K) *
          ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-((b / (2 * c)) * |η|))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c ^ m * K) * ENNReal.ofReal (2 / (b / (2 * c))) := by
        gcongr; exact lintegral_exp_neg_abs_le ha
    _ = ENNReal.ofReal (4 * K / b * c ^ (m + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.rpow_add hc0, Real.rpow_one]
        field_simp
        ring

end UnforcedLeray.Short.IIb.WeightNormAux
