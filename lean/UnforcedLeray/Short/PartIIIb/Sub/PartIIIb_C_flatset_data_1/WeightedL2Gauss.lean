import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.XNormDuality
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal NNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `1 + ρ ≤ (1 + κ) e^{ρ/κ}` for `κ > 0`, `ρ ≥ 0`. -/
theorem wg_lin_le_exp (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) :
    1 + ρ ≤ (1 + κ) * Real.exp (ρ / κ) := by
  have hk0 : κ ≠ 0 := hκ.ne'
  have ht0 : 0 ≤ ρ / κ := div_nonneg hρ hκ.le
  have e := Real.add_one_le_exp (ρ / κ)
  have hk : κ * (ρ / κ) = ρ := by
    field_simp
  have hpos : 0 ≤ (1 + κ) := by linarith
  nlinarith [mul_nonneg hpos (by linarith : (0:ℝ) ≤ Real.exp (ρ / κ) - (ρ / κ + 1))]

/-- Polynomial weight against a Gaussian: `(1+ρ)^m ≤ M e^{ρ/(16A)}` for `ρ ≥ 0`, some `M ≥ 0`. -/
theorem wg_pow_le (m A : ℝ) (hA : 0 < A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 0 ≤ ρ → (1 + ρ) ^ m ≤ M * Real.exp (ρ / (16 * A)) := by
  set N : ℕ := ⌈max m 0⌉₊ with hNdef
  have hN : m ≤ (N : ℝ) := le_trans (le_max_left m 0) (Nat.le_ceil _)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hκ : 0 < 16 * A * (N : ℝ) + 1 := by
    have : 0 ≤ 16 * A * (N : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hA.le) hN0
    linarith
  refine ⟨(1 + (16 * A * (N : ℝ) + 1)) ^ N, pow_nonneg (by linarith) N, fun ρ hρ => ?_⟩
  have h1 : (1 + ρ) ^ m ≤ (1 + ρ) ^ (N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hN
  rw [Real.rpow_natCast] at h1
  have h2 : 1 + ρ ≤ (1 + (16 * A * (N : ℝ) + 1)) * Real.exp (ρ / (16 * A * (N : ℝ) + 1)) :=
    wg_lin_le_exp _ ρ hκ hρ
  have h3 : (1 + ρ) ^ N ≤ ((1 + (16 * A * (N : ℝ) + 1)) *
      Real.exp (ρ / (16 * A * (N : ℝ) + 1))) ^ N := by
    gcongr
  have h4 : ((1 + (16 * A * (N : ℝ) + 1)) * Real.exp (ρ / (16 * A * (N : ℝ) + 1))) ^ N =
      (1 + (16 * A * (N : ℝ) + 1)) ^ N * Real.exp ((N : ℝ) * (ρ / (16 * A * (N : ℝ) + 1))) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  have hs : ρ / (16 * A * (N : ℝ) + 1) * (16 * A * (N : ℝ) + 1) = ρ := by
    field_simp
  have ht : ρ / (16 * A) * (16 * A) = ρ := by
    field_simp
  have hs0 : 0 ≤ ρ / (16 * A * (N : ℝ) + 1) := div_nonneg hρ hκ.le
  have h5 : (N : ℝ) * (ρ / (16 * A * (N : ℝ) + 1)) ≤ ρ / (16 * A) := by
    by_contra hcon
    push_neg at hcon
    have h16 : (0 : ℝ) < 16 * A := by linarith
    nlinarith [mul_lt_mul_of_pos_left hcon h16]
  have h6 : Real.exp ((N : ℝ) * (ρ / (16 * A * (N : ℝ) + 1))) ≤ Real.exp (ρ / (16 * A)) :=
    Real.exp_le_exp.2 h5
  have hpowM : (0 : ℝ) ≤ (1 + (16 * A * (N : ℝ) + 1)) ^ N := pow_nonneg (by linarith) N
  calc (1 + ρ) ^ m ≤ (1 + ρ) ^ N := h1
    _ ≤ ((1 + (16 * A * (N : ℝ) + 1)) * Real.exp (ρ / (16 * A * (N : ℝ) + 1))) ^ N := h3
    _ = (1 + (16 * A * (N : ℝ) + 1)) ^ N * Real.exp ((N : ℝ) * (ρ / (16 * A * (N : ℝ) + 1))) := h4
    _ ≤ (1 + (16 * A * (N : ℝ) + 1)) ^ N * Real.exp (ρ / (16 * A)) :=
        mul_le_mul_of_nonneg_left h6 hpowM

/-- The planar Gaussian `exp(-(x₁²+x₂²)/(16A))` is integrable on `ℝ × ℝ`. -/
theorem wg_gauss_integrable (A : ℝ) (hA : 0 < A) :
    Integrable (fun x : ℝ × ℝ => Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) := by
  have hb : 0 < 1 / (16 * A) := by positivity
  have h1 : Integrable (fun x : ℝ => Real.exp (-(1 / (16 * A)) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hprod : Integrable (fun z : ℝ × ℝ =>
      Real.exp (-(1 / (16 * A)) * z.1 ^ 2) * Real.exp (-(1 / (16 * A)) * z.2 ^ 2))
      (volume.prod volume) :=
    Integrable.mul_prod h1 h1
  refine hprod.congr (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-(1 / (16 * A)) * x.1 ^ 2) * Real.exp (-(1 / (16 * A)) * x.2 ^ 2) =
    Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))
  rw [← Real.exp_add]
  congr 1
  ring

/-- Points of the centred cell satisfy `|x₁| ≤ c/2`. -/
theorem wg_abs_of_mem_cell {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) : |x.1| ≤ c / 2 := by
  have hx1 : x.1 ∈ Set.Ico (-(c / 2)) (c / 2) := hx.1
  exact abs_le.2 ⟨hx1.1, hx1.2.le⟩

/-- **Weighted `L²` norm of a Gaussian on the cell, uniformly in `c`** (source 4562, 2828). -/
theorem weightedL2Gauss : WeightedL2Gauss := by
  intro m A hA
  obtain ⟨M, hM0, hM⟩ := wg_pow_le m A hA
  have hJint : Integrable (fun x : ℝ × ℝ => M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) :=
    (wg_gauss_integrable A hA).const_mul M
  set J : ℝ≥0∞ := ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)))
    with hJdef
  have hJfin : J < ⊤ := hJint.lintegral_lt_top
  refine ⟨J.toReal ^ (1 / 2 : ℝ), fun c hc h B _hmeas hbd => ?_⟩
  -- the constant `B` is nonnegative (evaluate the bound at the origin of the cell)
  have hB0 : 0 ≤ B := by
    have h0 := hbd (0, 0) (by
      show |(0 : ℝ)| ≤ c / 2
      rw [abs_zero]
      linarith)
    have hexp1 : Real.exp (-((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).1 ^ 2 +
        (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).2 ^ 2) / (16 * A)) = 1 := by
      simp
    rw [hexp1, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  -- pointwise bound of the integrand on the cell
  have hpt : ∀ x : ℝ × ℝ, (B0579.cell c).indicator
      (UnforcedLeray.Short.IIIa.XND.cw m h) x ≤
      ENNReal.ofReal (B ^ 2) *
        ENNReal.ofReal (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) := by
    intro x
    by_cases hx : x ∈ B0579.cell c
    · rw [Set.indicator_of_mem hx]
      show ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * ‖h x‖ₑ ^ 2 ≤ _
      have hx' : |x.1| ≤ c / 2 := wg_abs_of_mem_cell hx
      have hρ0 : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
      have hjb : B0579.jb x = 1 + (x.1 ^ 2 + x.2 ^ 2) := by
        unfold B0579.jb
        ring
      have hjbnn : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
      have hd : ((B0579.density m x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
        rw [← B0579.coe_density m x, ENNReal.ofReal_coe_nnreal]
      have hE : Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
          Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) = 1 := by
        rw [← Real.exp_add, show (x.1 ^ 2 + x.2 ^ 2) / (16 * A) + -(x.1 ^ 2 + x.2 ^ 2) / (16 * A)
          = 0 by ring, Real.exp_zero]
      have hjbM : B0579.jb x ^ m ≤ M * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (16 * A)) := by
        rw [hjb]
        exact hM _ hρ0
      have hbound := hbd x hx'
      have hsq : ‖h x‖ ^ 2 ≤ (B * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) ^ 2 := by
        nlinarith [norm_nonneg (h x)]
      have hreal : B0579.jb x ^ m * ‖h x‖ ^ 2 ≤ B ^ 2 * (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) := by
        have hMF : 0 ≤ M * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (16 * A)) :=
          mul_nonneg hM0 (Real.exp_pos _).le
        have step1 : B0579.jb x ^ m * ‖h x‖ ^ 2 ≤
            (M * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (16 * A))) *
              (B * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) ^ 2 :=
          mul_le_mul hjbM hsq (sq_nonneg _) hMF
        have step2 : (M * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (16 * A))) *
            (B * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) ^ 2 =
            B ^ 2 * (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) *
              (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
                Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) := by
          ring
        rw [hE, mul_one] at step2
        linarith [step1, step2]
      calc ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * ‖h x‖ₑ ^ 2
          = ENNReal.ofReal (B0579.jb x ^ m * ‖h x‖ ^ 2) := by
            rw [hd, ← ofReal_norm_eq_enorm, ENNReal.ofReal_mul hjbnn,
              ENNReal.ofReal_pow (norm_nonneg _)]
        _ ≤ ENNReal.ofReal (B ^ 2 * (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)))) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (B ^ 2) *
            ENNReal.ofReal (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) :=
            ENNReal.ofReal_mul (sq_nonneg _)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  -- lintegral bound, independent of `c`
  have hL : ∫⁻ x, ‖h x‖ₑ ^ 2 ∂(B0579.cellMeasure c m) ≤ ENNReal.ofReal (B ^ 2) * J := by
    rw [UnforcedLeray.Short.IIIa.XND.cellQ_eq c m h]
    calc ∫⁻ x : ℝ × ℝ, (B0579.cell c).indicator (UnforcedLeray.Short.IIIa.XND.cw m h) x
        ≤ ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (B ^ 2) *
            ENNReal.ofReal (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A))) :=
          by
            apply lintegral_mono
            intro x
            exact hpt x
      _ = ENNReal.ofReal (B ^ 2) * J := by
          rw [hJdef]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- take square roots
  have hBsq : ENNReal.ofReal (B ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal B := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg B) (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
    norm_num
  have hJrpow : J ^ (1 / 2 : ℝ) = ENNReal.ofReal (J.toReal ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hJfin.ne]
  have hC0 : 0 ≤ J.toReal ^ (1 / 2 : ℝ) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [UnforcedLeray.Short.IIIa.XND.eLpNorm_two_eq_lintegral']
  calc (∫⁻ x, ‖h x‖ₑ ^ 2 ∂(B0579.cellMeasure c m)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (B ^ 2) * J) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hL (by norm_num)
    _ = ENNReal.ofReal (B ^ 2) ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal B * ENNReal.ofReal (J.toReal ^ (1 / 2 : ℝ)) := by
        rw [hBsq, hJrpow]
    _ = ENNReal.ofReal (J.toReal ^ (1 / 2 : ℝ) * B) := by
        rw [← ENNReal.ofReal_mul hB0, mul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
