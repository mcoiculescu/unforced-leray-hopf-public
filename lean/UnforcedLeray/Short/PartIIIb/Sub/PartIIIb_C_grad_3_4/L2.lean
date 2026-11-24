import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4

/-!
# `PartIII-b:C/grad/3/4/2`: the uniform cell `L²` bound of the Gaussian lattice sum

Source `the November 2 reference manuscript`
5063-5079.  Proved: `gradLatticeL2`.

Route: a polynomial-weighted Gaussian is dominated by a Gaussian of half the rate
(`gl2_poly_gauss`); the lattice sum of a Gaussian with spacing `c ≥ 1` is bounded uniformly
(`gl2_gauss_sum`, a copy of the `gauss_shift_aux` argument with an arbitrary rate); hence
`latticeS² ≤ K² e^{-α η²}` pointwise, uniformly in `c ≥ 1`, and the normalized cell integral of
a function of `η` alone is its `η`-integral (`gl2_lint_avg_snd`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A polynomially weighted Gaussian is dominated by a Gaussian of half the rate. -/
theorem gl2_poly_gauss (n : ℕ) (γ t : ℝ) (hγ : 0 < γ) :
    (1 + |t|) ^ n * Real.exp (-γ * t ^ 2) ≤
      Real.exp ((n : ℝ) ^ 2 / (2 * γ)) * Real.exp (-(γ / 2) * t ^ 2) := by
  have h1 : (1 + |t|) ^ n ≤ Real.exp ((n : ℝ) * |t|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |t|]) n
  have key : (n : ℝ) * |t| - γ / 2 * t ^ 2 ≤ (n : ℝ) ^ 2 / (2 * γ) := by
    rw [le_div_iff₀ (by linarith)]
    rw [← sq_abs t]
    nlinarith [sq_nonneg ((n : ℝ) - γ * |t|)]
  calc (1 + |t|) ^ n * Real.exp (-γ * t ^ 2)
      ≤ Real.exp ((n : ℝ) * |t|) * Real.exp (-γ * t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * |t| - γ / 2 * t ^ 2) * Real.exp (-(γ / 2) * t ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp ((n : ℝ) ^ 2 / (2 * γ)) * Real.exp (-(γ / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 key) (Real.exp_pos _).le

/-- Lattice sum of a Gaussian of arbitrary rate `β > 0` with spacing `c ≥ 1`, uniformly in the
centre `y`: summable, and bounded by `2 ∑_m e^{-β m}` (same argument as `gauss_shift_aux`). -/
theorem gl2_gauss_sum (β : ℝ) (hβ : 0 < β) (c : ℝ) (hc : 1 ≤ c) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-β * (y - n * c) ^ 2)) ∧
      ∑' n : ℤ, Real.exp (-β * (y - n * c) ^ 2) ≤ 2 * ∑' m : ℕ, Real.exp (-β * m) := by
  have hc0 : 0 < c := by linarith
  set N : ℤ := ⌈y / c⌉ with hN
  set f : ℤ → ℝ := fun n => Real.exp (-β * (y - n * c) ^ 2) with hf
  have hNy : y ≤ N * c := by
    have := Int.le_ceil (y / c)
    rwa [div_le_iff₀ hc0] at this
  have hNy' : ((N : ℝ) - 1) * c < y := by
    have := Int.ceil_lt_add_one (y / c)
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hc0] at this
    exact this
  have hkey : ∀ (x : ℝ) (m : ℕ), (m : ℝ) * c ≤ |y - x| →
      Real.exp (-β * (y - x) ^ 2) ≤ Real.exp (-β * m) := by
    intro x m hm
    refine Real.exp_le_exp.2 ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hsq : ((m : ℝ) * c) ^ 2 ≤ (y - x) ^ 2 := by
      rw [← sq_abs (y - x)]
      exact pow_le_pow_left₀ (by positivity) hm 2
    have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        nlinarith
    have hc2 : (1 : ℝ) ≤ c ^ 2 := by nlinarith
    have h1 : (m : ℝ) ≤ (y - x) ^ 2 := by
      calc (m : ℝ) ≤ (m : ℝ) ^ 2 := hmm
        _ ≤ (m : ℝ) ^ 2 * c ^ 2 := le_mul_of_one_le_right (by positivity) hc2
        _ = ((m : ℝ) * c) ^ 2 := by ring
        _ ≤ (y - x) ^ 2 := hsq
    nlinarith
  have hshift : Summable (fun n : ℤ => f (N + n)) ∧
      ∑' n : ℤ, f (N + n) ≤ 2 * ∑' m : ℕ, Real.exp (-β * m) := by
    refine UnforcedLeray.Gaussian.tsum_int_le_of_le_two_sides (fun n => (Real.exp_pos _).le)
      (UnforcedLeray.Gaussian.summable_exp_neg_mul_nat hβ) (fun m => ?_) (fun m => ?_)
    · refine hkey _ m ?_
      push_cast
      have : (m : ℝ) * c ≤ (N + m) * c - y := by nlinarith
      rw [abs_sub_comm, abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) m])]
      linarith
    · refine hkey _ m ?_
      push_cast
      have hmc : (0 : ℝ) ≤ m * c := by positivity
      have : (m : ℝ) * c ≤ y - (N + -((m : ℝ) + 1)) * c := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      exact this
  refine ⟨?_, ?_⟩
  · have := hshift.1.comp_injective (add_right_injective (-N))
    refine this.congr fun n => ?_
    simp
  · have heq : ∑' n : ℤ, f n = ∑' n : ℤ, f (N + n) :=
      ((Equiv.addLeft N).tsum_eq f).symm
    rw [heq]
    exact hshift.2

/-- The Gaussian weight of the lattice sum as a function of `(u, η)`, bounded by a product of a
`u`-Gaussian and an `η`-Gaussian with constant `P² = exp(k²/α)²`. -/
theorem gl2_W_le (α : ℝ) (hα : 0 < α) (k : ℕ) (u η : ℝ) :
    latticeW α k u η ≤ Real.exp ((k : ℝ) ^ 2 / (2 * α)) ^ 2 * Real.exp (-(α / 2) * η ^ 2) *
      Real.exp (-(α / 2) * u ^ 2) := by
  unfold latticeW
  have hu := gl2_poly_gauss k α u hα
  have hη := gl2_poly_gauss k α η hα
  have h1 : (1 + |u| + |η|) ^ k ≤ (1 + |u|) ^ k * (1 + |η|) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (abs_nonneg u) (abs_nonneg η)]
  have he : Real.exp (-α * (u ^ 2 + η ^ 2)) = Real.exp (-α * u ^ 2) * Real.exp (-α * η ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc (1 + |u| + |η|) ^ k * (Real.exp (-α * u ^ 2) * Real.exp (-α * η ^ 2))
      ≤ ((1 + |u|) ^ k * (1 + |η|) ^ k) * (Real.exp (-α * u ^ 2) * Real.exp (-α * η ^ 2)) := by
        apply mul_le_mul_of_nonneg_right h1
        positivity
    _ = ((1 + |u|) ^ k * Real.exp (-α * u ^ 2)) * ((1 + |η|) ^ k * Real.exp (-α * η ^ 2)) := by
        ring
    _ ≤ (Real.exp ((k : ℝ) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * u ^ 2)) *
          (Real.exp ((k : ℝ) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * η ^ 2)) :=
        mul_le_mul hu hη (by positivity) (by positivity)
    _ = Real.exp ((k : ℝ) ^ 2 / (2 * α)) ^ 2 * Real.exp (-(α / 2) * η ^ 2) *
          Real.exp (-(α / 2) * u ^ 2) := by ring

/-- The constant `K = P² · 2 ∑_m e^{-(α/2) m}` of the lattice-sum envelope. -/
def gl2K (α : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) ^ 2 / (2 * α)) ^ 2 * (2 * ∑' m : ℕ, Real.exp (-(α / 2) * m))

theorem gl2_latticeW_nonneg (α : ℝ) (k : ℕ) (u η : ℝ) : 0 ≤ latticeW α k u η := by
  unfold latticeW
  positivity

/-- Pointwise envelope: `latticeS α k c x ≤ K e^{-(α/2) η²}`, uniformly in `c ≥ 1` and `x`. -/
theorem gl2_latticeS_le (α : ℝ) (hα : 0 < α) (k : ℕ) (c : ℝ) (hc : 1 ≤ c) (x : ℝ × ℝ) :
    latticeS α k c x ≤ gl2K α k * Real.exp (-(α / 2) * x.2 ^ 2) := by
  have hsumm : Summable (fun j : ℤ => Real.exp (-(α / 2) * (x.1 - j * c) ^ 2)) :=
    (gl2_gauss_sum (α / 2) (by positivity) c hc x.1).1
  have hbound := (gl2_gauss_sum (α / 2) (by positivity) c hc x.1).2
  set P2e : ℝ := Real.exp ((k : ℝ) ^ 2 / (2 * α)) ^ 2 * Real.exp (-(α / 2) * x.2 ^ 2) with hP2e
  have hterm : ∀ j : ℤ, latticeW α k (x.1 - (j : ℝ) * c) x.2 ≤
      P2e * Real.exp (-(α / 2) * (x.1 - j * c) ^ 2) := by
    intro j
    rw [hP2e, mul_assoc]
    have := gl2_W_le α hα k (x.1 - (j : ℝ) * c) x.2
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hsumm2 : Summable (fun j : ℤ => P2e * Real.exp (-(α / 2) * (x.1 - j * c) ^ 2)) :=
    hsumm.mul_left _
  have hlat : Summable (fun j : ℤ => latticeW α k (x.1 - (j : ℝ) * c) x.2) :=
    Summable.of_nonneg_of_le (fun j => gl2_latticeW_nonneg α k _ _) hterm hsumm2
  unfold latticeS
  calc ∑' j : ℤ, latticeW α k (x.1 - (j : ℝ) * c) x.2
      ≤ ∑' j : ℤ, P2e * Real.exp (-(α / 2) * (x.1 - j * c) ^ 2) :=
        hlat.tsum_le_tsum hterm hsumm2
    _ = P2e * ∑' j : ℤ, Real.exp (-(α / 2) * (x.1 - j * c) ^ 2) := tsum_mul_left
    _ ≤ P2e * (2 * ∑' m : ℕ, Real.exp (-(α / 2) * m)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = gl2K α k * Real.exp (-(α / 2) * x.2 ^ 2) := by
        rw [hP2e, gl2K]
        ring

/-- The `L²`-cell integral of a function of `η` alone, against the normalized cell measure, is
its `η`-integral (`dq/c` over a `q`-interval of length `c`). -/
theorem gl2_lint_avg_snd (c : ℝ) (hc : 0 < c) (F : ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x.2 ∂(UnforcedLeray.Cyl.avgμ c) = ∫⁻ η, F η := by
  have hm : Measurable (fun z : ℝ × ℝ => F z.2) := hF.comp measurable_snd
  rw [UnforcedLeray.Cyl.avgμ, lintegral_smul_measure, UnforcedLeray.Cyl.cellμ_eq_prod,
    lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico, smul_eq_mul]
  rw [show c / 2 - -c / 2 = c by ring, mul_comm _ (ENNReal.ofReal c), ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one,
    one_mul]

theorem gradLatticeL2 : GradLatticeL2 := by
  intro α hα k
  refine ⟨∫ η : ℝ, gl2K α k ^ 2 * Real.exp (-α * η ^ 2), ?_, ?_⟩
  · apply integral_nonneg
    intro η
    positivity
  intro c hc
  have hint : Integrable (fun η : ℝ => gl2K α k ^ 2 * Real.exp (-α * η ^ 2)) :=
    (integrable_exp_neg_mul_sq hα).const_mul _
  have hnn : ∀ η : ℝ, 0 ≤ gl2K α k ^ 2 * Real.exp (-α * η ^ 2) := fun η => by positivity
  have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (latticeS α k c x ^ 2) ≤
      ENNReal.ofReal (gl2K α k ^ 2 * Real.exp (-α * x.2 ^ 2)) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    have h := gl2_latticeS_le α hα k c hc x
    have h0 : 0 ≤ latticeS α k c x := tsum_nonneg (fun j => gl2_latticeW_nonneg α k _ _)
    have he2 : Real.exp (-(α / 2) * x.2 ^ 2) ^ 2 = Real.exp (-α * x.2 ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc latticeS α k c x ^ 2 ≤ (gl2K α k * Real.exp (-(α / 2) * x.2 ^ 2)) ^ 2 :=
          pow_le_pow_left₀ h0 h 2
      _ = gl2K α k ^ 2 * Real.exp (-α * x.2 ^ 2) := by
          rw [mul_pow, he2]
  have hmeas : Measurable (fun η : ℝ => ENNReal.ofReal (gl2K α k ^ 2 * Real.exp (-α * η ^ 2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  calc ∫⁻ x, ENNReal.ofReal (latticeS α k c x ^ 2) ∂(UnforcedLeray.Cyl.avgμ c)
      ≤ ∫⁻ x, ENNReal.ofReal (gl2K α k ^ 2 * Real.exp (-α * x.2 ^ 2)) ∂(UnforcedLeray.Cyl.avgμ c) :=
        lintegral_mono hpt
    _ = ∫⁻ η, ENNReal.ofReal (gl2K α k ^ 2 * Real.exp (-α * η ^ 2)) :=
        gl2_lint_avg_snd c (by linarith) _ hmeas
    _ = ENNReal.ofReal (∫ η : ℝ, gl2K α k ^ 2 * Real.exp (-α * η ^ 2)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)).symm

end UnforcedLeray.Short.PartIIIb.Concrete
