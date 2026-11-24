import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_3
import UnforcedLeray.Short.PartIIIa.ComposeCorollary

/-!
# `flatMultFunBound_of` (source 3566-3567, 2714-2729)

From the actual train multiplier bound `FlatTrainMultBound` (`sup √s W |v| ≤ C ν^{-k}` on the
chart, `NearInst/Targets.lean`) we get `FlatMultFunBound`: for measurable `u`,
`‖M₀u‖_{𝒵₁} ≤ 2C ν^{-k} ‖u‖_𝓗`.

Route: `|v⊗u + u⊗v|_F ≤ 2|v||u|` pointwise; then the weights
`s^{-1/2}` (for `ageμ c (-1/2)`) and `s^{-3/2}` (for `ageμ c (-3/2)`) differ by the factor `s`,
which is absorbed by `(√s W|v|)² ≤ M²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.IIIa

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem norm_add_sq_le_two (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by gcongr
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The Frobenius norm of `a ⊗ u + u ⊗ a` is at most `2 |a| |u|`. -/
theorem tnorm2_flatMult_le (a : Fin 2 → ℝ) (u : Fin 2 → ℂ) :
    tnorm2 (fun i j => ((a i : ℝ) : ℂ) * u j + u i * ((a j : ℝ) : ℂ)) ≤
      2 * vnorm2 (fun i => ((a i : ℝ) : ℂ)) * vnorm2 u := by
  unfold tnorm2 vnorm2
  dsimp only
  have hA0 : 0 ≤ ∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hU0 : 0 ≤ ∑ i : Fin 2, ‖u i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : ∑ i : Fin 2, ∑ j : Fin 2,
      ‖((a i : ℝ) : ℂ) * u j + u i * ((a j : ℝ) : ℂ)‖ ^ 2 ≤
        4 * (∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2) * (∑ i : Fin 2, ‖u i‖ ^ 2) := by
    have hterm : ∀ i j : Fin 2,
        ‖((a i : ℝ) : ℂ) * u j + u i * ((a j : ℝ) : ℂ)‖ ^ 2 ≤
          2 * (‖((a i : ℝ) : ℂ)‖ ^ 2 * ‖u j‖ ^ 2) + 2 * (‖u i‖ ^ 2 * ‖((a j : ℝ) : ℂ)‖ ^ 2) := by
      intro i j
      have h := norm_add_sq_le_two (((a i : ℝ) : ℂ) * u j) (u i * ((a j : ℝ) : ℂ))
      rw [norm_mul, norm_mul] at h
      nlinarith [h]
    simp only [Fin.sum_univ_two] at hterm ⊢
    nlinarith [hterm 0 0, hterm 0 1, hterm 1 0, hterm 1 1]
  have h4 : Real.sqrt (4 * (∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2) * (∑ i : Fin 2, ‖u i‖ ^ 2)) =
      2 * Real.sqrt (∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2) * Real.sqrt (∑ i : Fin 2, ‖u i‖ ^ 2) := by
    rw [show 4 * (∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2) * (∑ i : Fin 2, ‖u i‖ ^ 2) =
        (2 * Real.sqrt (∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2) * Real.sqrt (∑ i : Fin 2, ‖u i‖ ^ 2)) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hU0]; ring]
    exact Real.sqrt_sq (by positivity)
  calc Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
        ‖((a i : ℝ) : ℂ) * u j + u i * ((a j : ℝ) : ℂ)‖ ^ 2)
      ≤ Real.sqrt (4 * (∑ i : Fin 2, ‖((a i : ℝ) : ℂ)‖ ^ 2) * (∑ i : Fin 2, ‖u i‖ ^ 2)) :=
        Real.sqrt_le_sqrt key
    _ = _ := h4

/-- `‖ṽ‖` of the chart coefficient: the Euclidean norm of the train coefficient at a chart point. -/
theorem vnorm2_trainVel_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (p : ℝ × (ℝ × ℝ)) :
    vnorm2 (fun i => ((UnforcedLeray.Short.IIIa.trainVel tr p.1 p.2 i : ℝ) : ℂ)) =
      ‖trainMer tr p‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold vnorm2
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [trainMer, Complex.norm_real]

/-- Real inequality: the weighted pointwise bound. -/
theorem real_key {s W x t y M : ℝ} (hs : 0 < s) (hW : 0 ≤ W) (hx : 0 ≤ x) (hxt : x ≤ 2 * t * y)
    (hM : Real.sqrt s * W * t ≤ M) (hM0 : 0 ≤ M) (ht : 0 ≤ t) :
    s ^ (-1 / 2 : ℝ) * (W * x) ^ 2 ≤ s ^ (-3 / 2 : ℝ) * ((2 * M) ^ 2 * y ^ 2) := by
  have hs12 : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
    rw [show (-1 / 2 : ℝ) = -3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]
  have hA0 : 0 ≤ Real.sqrt s * W * t := mul_nonneg (mul_nonneg (Real.sqrt_nonneg s) hW) ht
  have hM2 : (Real.sqrt s * W * t) ^ 2 ≤ M ^ 2 := by nlinarith
  have hWt : s * (W * t) ^ 2 ≤ M ^ 2 := by
    have e : (Real.sqrt s * W * t) ^ 2 = s * (W * t) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hs.le]; ring
    linarith
  have h3 : (W * x) ^ 2 ≤ (2 * t * y * W) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hxt hW
    nlinarith [mul_nonneg hW hx]
  have h4 : s * (W * x) ^ 2 ≤ (2 * M) ^ 2 * y ^ 2 := by
    have h5 : s * (W * x) ^ 2 ≤ s * (2 * t * y * W) ^ 2 := mul_le_mul_of_nonneg_left h3 hs.le
    have h6 : s * (2 * t * y * W) ^ 2 = 4 * y ^ 2 * (s * (W * t) ^ 2) := by ring
    have h7 : 4 * y ^ 2 * (s * (W * t) ^ 2) ≤ 4 * y ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hWt (by positivity)
    nlinarith
  rw [hs12]
  calc s ^ (-3 / 2 : ℝ) * s * (W * x) ^ 2 = s ^ (-3 / 2 : ℝ) * (s * (W * x) ^ 2) := by ring
    _ ≤ s ^ (-3 / 2 : ℝ) * ((2 * M) ^ 2 * y ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hs.le _)

theorem enorm_sq_eq_ofReal (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]

/-- Reduction of `eLpNorm` at exponent `2` to a weighted `lintegral` comparison. -/
theorem eLpNorm_two_le_of_sq {α : Type*} [MeasurableSpace α] {μ1 μ3 : Measure α}
    {g h : α → ℝ} {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (H : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ1 ≤ ∫⁻ x, a ^ 2 * ‖h x‖ₑ ^ 2 ∂μ3) :
    eLpNorm g 2 μ1 ≤ a * eLpNorm h 2 μ3 := by
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ha)] at H
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero h2top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero h2top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ1) ^ (1 / 2 : ℝ)
      ≤ (a ^ 2 * ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ3) ^ (1 / 2 : ℝ) := by
        exact ENNReal.rpow_le_rpow H (by norm_num)
    _ = a * (∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ3) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

theorem measurable_transWeight' (mZ : ℝ) : Measurable fun p : ℝ × (ℝ × ℝ) => transWeight mZ p := by
  unfold transWeight
  fun_prop

theorem measurable_tnorm2_flatMult {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i) :
    Measurable fun p => tnorm2 (flatMult tr u p) := by
  unfold tnorm2
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
  exact Finset.measurable_sum _ fun j _ => ((measurable_flatMult tr hu i j).norm).pow_const 2

theorem measurable_vnorm2_apply {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i) :
    Measurable fun p => vnorm2 (u p) := by
  unfold vnorm2
  exact Measurable.sqrt (Finset.measurable_sum _ fun i _ => ((hu i).norm).pow_const 2)

/-- **`flatMultFunBound_of`** (source 3566-3567): the actual train multiplier bound gives the
function-level bound `FlatMultFunBound`. -/
theorem flatMultFunBound_of (hT : FlatTrainMultBound) : FlatMultFunBound := by
  unfold FlatMultFunBound
  intro mZ hmZ
  unfold FlatTrainMultBound at hT
  obtain ⟨C, k, ν₀, hν₀, hbd⟩ := hT mZ hmZ
  refine ⟨2 * max C 0, k, ν₀, hν₀, ?_⟩
  intro ν hν tr htr u hu
  have hν0 : 0 < ν := hν.1
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hcEq : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
    rw [Real.rpow_neg hν0.le, Real.rpow_two]
  obtain ⟨hmeas, hpt⟩ := hbd ν hν (ν ^ (-2 : ℝ)) hcEq tr htr
  have hinv : 0 ≤ ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν0.le) _
  have hM : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 →
      Real.sqrt p.1 * transWeight mZ p * ‖trainMer tr p‖ ≤ max C 0 * ν⁻¹ ^ k := fun p hp =>
    (hpt p hp).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) hinv)
  have hM0 : 0 ≤ max C 0 * ν⁻¹ ^ k := mul_nonneg (le_max_right C 0) hinv
  have hexp : ν ^ (-(k : ℝ)) = ν⁻¹ ^ k := by
    rw [Real.rpow_neg hν0.le, Real.rpow_natCast, inv_pow]
  rw [hexp]
  rw [show 2 * max C 0 * ν⁻¹ ^ k = 2 * (max C 0 * ν⁻¹ ^ k) by ring]
  set M := max C 0 * ν⁻¹ ^ k with hMdef
  have hgM := measurable_transWeight' mZ
  have hgMeas : Measurable fun p : ℝ × (ℝ × ℝ) => transWeight mZ p * tnorm2 (flatMult tr u p) :=
    hgM.mul (measurable_tnorm2_flatMult tr hu)
  have hhMeas := measurable_vnorm2_apply hu
  unfold z1Norm2 hCalNorm
  apply eLpNorm_two_le_of_sq ENNReal.ofReal_ne_top
  have hf1 : Measurable fun p : ℝ × (ℝ × ℝ) => ‖transWeight mZ p * tnorm2 (flatMult tr u p)‖ₑ ^ 2 :=
    (hgMeas.enorm).pow_const 2
  have hf2 : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (2 * M) ^ 2 * ‖vnorm2 (u p)‖ₑ ^ 2 :=
    ((hhMeas.enorm).pow_const 2).const_mul _
  rw [lintegral_ageμ hc (-1 / 2) hf1, lintegral_ageμ hc (-3 / 2) hf2]
  apply setLIntegral_mono' (measurableSet_halfCell (ν ^ (-2 : ℝ)))
  intro p hp
  have hs : 0 < p.1 := hp.1
  have hx : tnorm2 (flatMult tr u p) ≤
      2 * ‖trainMer tr p‖ * vnorm2 (u p) := by
    have h := tnorm2_flatMult_le (fun i => UnforcedLeray.Short.IIIa.trainVel tr p.1 p.2 i) (u p)
    rw [vnorm2_trainVel_eq] at h
    exact h
  have hW : 0 ≤ transWeight mZ p := by
    unfold transWeight; positivity
  have hxnn : 0 ≤ tnorm2 (flatMult tr u p) := Real.sqrt_nonneg _
  have hynn : 0 ≤ vnorm2 (u p) := Real.sqrt_nonneg _
  have hreal := real_key hs hW hxnn hx (hM p hs) hM0 (norm_nonneg _)
  have hcpos : 0 ≤ (ν ^ (-2 : ℝ))⁻¹ := (inv_nonneg.2 hc.le)
  have hA : 0 ≤ (ν ^ (-2 : ℝ))⁻¹ * p.1 ^ (-1 / 2 : ℝ) :=
    mul_nonneg hcpos (Real.rpow_nonneg hs.le _)
  have hB : 0 ≤ (ν ^ (-2 : ℝ))⁻¹ * p.1 ^ (-3 / 2 : ℝ) :=
    mul_nonneg hcpos (Real.rpow_nonneg hs.le _)
  have hM2 : 0 ≤ (2 * M) ^ 2 := by positivity
  have hG : ‖transWeight mZ p * tnorm2 (flatMult tr u p)‖ₑ ^ 2 =
      ENNReal.ofReal ((transWeight mZ p * tnorm2 (flatMult tr u p)) ^ 2) := enorm_sq_eq_ofReal _
  have hH : ‖vnorm2 (u p)‖ₑ ^ 2 = ENNReal.ofReal (vnorm2 (u p) ^ 2) := enorm_sq_eq_ofReal _
  rw [hG, hH, ← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 2 * M)]
  rw [← ENNReal.ofReal_mul hM2, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB]
  apply ENNReal.ofReal_le_ofReal
  have hmul := mul_le_mul_of_nonneg_left hreal (inv_nonneg.2 hc.le)
  calc (ν ^ (-2 : ℝ))⁻¹ * p.1 ^ (-1 / 2 : ℝ) * (transWeight mZ p * tnorm2 (flatMult tr u p)) ^ 2
      = (ν ^ (-2 : ℝ))⁻¹ * (p.1 ^ (-1 / 2 : ℝ) * (transWeight mZ p * tnorm2 (flatMult tr u p)) ^ 2) := by
        ring
    _ ≤ (ν ^ (-2 : ℝ))⁻¹ * (p.1 ^ (-3 / 2 : ℝ) * ((2 * M) ^ 2 * vnorm2 (u p) ^ 2)) := hmul
    _ = (ν ^ (-2 : ℝ))⁻¹ * p.1 ^ (-3 / 2 : ℝ) * ((2 * M) ^ 2 * vnorm2 (u p) ^ 2) := by ring

end UnforcedLeray.Short.PartIIIb.NearInst
