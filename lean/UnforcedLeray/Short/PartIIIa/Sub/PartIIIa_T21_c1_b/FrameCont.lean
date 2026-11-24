import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# Continuity of the periodized frame rows (helper of `PartIII-a:T21/c1/b`, SP 2891-2897)

Source of record: `the November 2 reference manuscript`, lines 2891-2897.

For `d > 0` the periodized growing vectors `E_i = P_d e_i`, the unnormalised dual rows
`Λ⁰_i = P_d λ_i` and the normalised rows `Λ_i = Σ_j (G⁻¹)_{ij} Λ⁰_j` are continuous: `e_i`
(Gaussian tails, `e_decay`) and `λ_i` (`O(|y|^{-2})`, `lamP_decay`) obey the translate bound
`C (1 + |y₁|)^{-2}`, so the sum of translates converges locally uniformly
(`Gaussian.continuous_tsum_translates`).

`exists_aesm_replacement`: an input `W` of a continuous row `Λ` with `Λ W` integrable may be
replaced by the a.e.-strongly measurable `1_{Λ ≠ 0} W`, which has the same `Λ W` and a smaller
modulus. This lets a dual bound proved for measurable inputs act on every input.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.FrameCont

/-- `x^{-2} = (x⁻¹)²` for `x ≥ 0`. -/
lemma rpow_neg_two_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = (x⁻¹) ^ 2 := by
  rw [Real.rpow_neg hx, Real.rpow_two, inv_pow]

/-- The Gaussian is dominated by the translate weight: `e^{-(a²+b²)/8} ≤ 16 (1+|a|)^{-2}`. -/
lemma exp_le_translate_weight (a b : ℝ) :
    Real.exp (-(a ^ 2 + b ^ 2) / 8) ≤ 16 * (1 + |a|) ^ (-(2 : ℝ)) := by
  have hpos : 0 < 1 + |a| := by positivity
  rw [rpow_neg_two_eq _ hpos.le, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : Real.exp (-(a ^ 2 + b ^ 2) / 8) ≤ Real.exp (-(a ^ 2) / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg b])
  have h2 : a ^ 2 / 8 + 1 ≤ Real.exp (a ^ 2 / 8) := Real.add_one_le_exp _
  have h3 : Real.exp (-(a ^ 2) / 8) * Real.exp (a ^ 2 / 8) = 1 := by
    rw [← Real.exp_add]
    have : -(a ^ 2) / 8 + a ^ 2 / 8 = 0 := by ring
    rw [this, Real.exp_zero]
  have h4 : (1 + |a|) ^ 2 ≤ 16 * Real.exp (a ^ 2 / 8) := by
    nlinarith [abs_nonneg a, sq_abs a, sq_nonneg (|a| - 1)]
  calc Real.exp (-(a ^ 2 + b ^ 2) / 8) * (1 + |a|) ^ 2
      ≤ Real.exp (-(a ^ 2) / 8) * (16 * Real.exp (a ^ 2 / 8)) :=
        mul_le_mul h1 h4 (by positivity) (Real.exp_pos _).le
    _ = 16 * (Real.exp (-(a ^ 2) / 8) * Real.exp (a ^ 2 / 8)) := by ring
    _ = 16 := by rw [h3, mul_one]

/-- The growing vectors obey the translate bound `C (1 + |y₁|)^{-2}` (from `e_decay`). -/
theorem e_translate_bound (κ : PlanarFrameKernels) :
    ∃ C : ℝ, ∀ i z, ‖κ.e i z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  refine ⟨16 * |C|, fun i z => ?_⟩
  calc ‖κ.e i z‖ ≤ C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := hC i z
    _ ≤ |C| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (exp_le_translate_weight z.1 z.2) (abs_nonneg C)
    _ = 16 * |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

/-- The planar dual kernels obey the translate bound `C (1 + |y₁|)^{-2}` (from `lamP_decay`). -/
theorem lamP_translate_bound (κ : PlanarFrameKernels) :
    ∃ C : ℝ, ∀ i z, ‖κ.lamP i z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := κ.lamP_decay
  refine ⟨|C|, fun i z => ?_⟩
  refine (hC i z).trans ?_
  rw [rpow_neg_two_eq _ (by positivity)]
  have h1 : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith [abs_nonneg z.2])
  have h2 : ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ ((1 + |z.1|)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  calc C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ |C| * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + |z.1|)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)

/-- The periodization `P_d f` of a continuous `f` with a translate bound is continuous. -/
theorem perSum_continuous {f : ℝ × ℝ → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) {d : ℝ} (hd : d ≠ 0) :
    Continuous (perSum d f) := by
  have heq : perSum d f = fun y => ∑' n : ℤ, f (y - Gaussian.shiftVec (-d) n) := by
    funext y
    unfold perSum
    refine tsum_congr fun n => ?_
    congr 1
    ext <;> simp [Gaussian.shiftVec]
  rw [heq]
  exact Gaussian.continuous_tsum_translates hf (s := 2) (c := -d) (C := C) (by norm_num)
    (neg_ne_zero.2 hd) hC

/-- `E_i = P_d e_i` is continuous for `d > 0`. -/
theorem perE_continuous (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d) (i : Fin 2) :
    Continuous (perE κ d i) := by
  obtain ⟨C, hC⟩ := e_translate_bound κ
  exact perSum_continuous (κ.e_cont i) (hC i) hd.ne'

/-- `Λ⁰_i = P_d λ_i` is continuous for `d > 0`. -/
theorem perLam0_continuous (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d) (i : Fin 2) :
    Continuous (perLam0 κ d i) := by
  obtain ⟨C, hC⟩ := lamP_translate_bound κ
  exact perSum_continuous (κ.lamP_cont i) (hC i) hd.ne'

/-- The normalised rows `Λ_i = Σ_j (G⁻¹)_{ij} Λ⁰_j` are continuous for `d > 0`. -/
theorem perLam_continuous (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d) (i : Fin 2) :
    Continuous (perLam κ d i) := by
  unfold perLam
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (perLam0_continuous κ hd j)

/-- An input `W` of a continuous row `Λ` with `Λ W` integrable can be replaced by the
a.e.-strongly measurable `W' = 1_{Λ ≠ 0} W`: `|W'| ≤ |W|` and `Λ W' = Λ W` pointwise. -/
theorem exists_aesm_replacement {μ : Measure (ℝ × ℝ)} {Λ W : ℝ × ℝ → ℂ} (hΛ : Continuous Λ)
    (hI : Integrable (fun x => Λ x * W x) μ) :
    ∃ W' : ℝ × ℝ → ℂ, AEStronglyMeasurable W' μ ∧ (∀ x, ‖W' x‖ ≤ ‖W x‖) ∧
      ∀ x, Λ x * W' x = Λ x * W x := by
  refine ⟨(Λ ⁻¹' {0}ᶜ).indicator W, ?_, fun x => norm_indicator_le_norm_self _ _, fun x => ?_⟩
  · have hS : MeasurableSet (Λ ⁻¹' {0}ᶜ) := hΛ.measurable (measurableSet_singleton 0).compl
    have heq : (Λ ⁻¹' {0}ᶜ).indicator W =
        (Λ ⁻¹' {0}ᶜ).indicator (fun x => (Λ x)⁻¹ * (Λ x * W x)) := by
      funext x
      by_cases hx : Λ x = 0
      · have hx' : x ∉ Λ ⁻¹' {0}ᶜ := by simpa using hx
        rw [indicator_of_notMem hx', indicator_of_notMem hx']
      · have hx' : x ∈ Λ ⁻¹' {0}ᶜ := by simpa using hx
        rw [indicator_of_mem hx', indicator_of_mem hx', inv_mul_cancel_left₀ hx]
    rw [heq]
    exact (hΛ.measurable.inv.aestronglyMeasurable.mul hI.aestronglyMeasurable).indicator hS
  · by_cases hx : Λ x = 0
    · rw [hx, zero_mul, zero_mul]
    · have hx' : x ∈ Λ ⁻¹' {0}ᶜ := by simpa using hx
      rw [indicator_of_mem hx']

end UnforcedLeray.Short.IIIa.FrameCont
