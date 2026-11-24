import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.Leaves
import UnforcedLeray.Units.B0191
import UnforcedLeray.Units.B0284.Defs
import UnforcedLeray.Units.B0579
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/7`: rapid decay of the smoothed tests (`AdjSmoothDecay`)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(the free part of the Volterra iteration on `X_{-m,c}`) and 3044-3050 (weights on the cell).

Pure smoothing fact: for a cylinder test `ψ` with `ψ = 0` for `|η| > R`, the planar Gaussian
smoothing `P_θ ψ = cylHeatSmooth c θ ψ` satisfies `|P_θ ψ(x)| ≤ C (1 + η²)^{-k}` uniformly in
`θ ∈ [0, Θ]`. For `|η| ≥ 2A` (with `A = |R| + 1`) only the points `w` with `|w.2| ≥ |η|/2`
contribute to the convolution, and the Chebyshev bound `1 ≤ (w.2 / t)^{2n}` with the Gaussian
moments `∫ w.2^{2n} G_θ ≤ 2 n! (8θ)^n` gives the decay `|η|^{-2n}`; for `|η| < 2A` the sup bound
is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.B0284 (heatKernel2)

/-- The one-dimensional kernel in the form `(√(4πθ))⁻¹ e^{-(1/(4θ)) s²}`. -/
theorem adjSD_g_eq (θ s : ℝ) : UnforcedLeray.B0191.heatKernel 1 θ s
    = (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (4 * θ)) * s ^ 2) := by
  have e1 : 4 * Real.pi * 1 * θ = 4 * Real.pi * θ := by ring
  have e2 : -s ^ 2 / (4 * 1 * θ) = -(1 / (4 * θ)) * s ^ 2 := by ring
  unfold UnforcedLeray.B0191.heatKernel
  rw [e1, e2]

/-- Pointwise moment bound: `s^{2n} G_θ(s) ≤ n! (8θ)^n (√(4πθ))⁻¹ e^{-s²/(8θ)}`. -/
theorem adjSD_moment_pointwise {θ : ℝ} (hθ : 0 < θ) (n : ℕ) (s : ℝ) :
    s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s
      ≤ (n.factorial * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
        * Real.exp (-(1 / (8 * θ)) * s ^ 2) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have h8 : (0:ℝ) < 8 * θ := by linarith
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h1 : (s ^ 2 / (8 * θ)) ^ n / (n.factorial : ℝ) ≤ Real.exp (s ^ 2 / (8 * θ)) :=
    Real.pow_div_factorial_le_exp (s ^ 2 / (8 * θ)) (div_nonneg (sq_nonneg s) h8.le) n
  have h4 : (s ^ 2 / (8 * θ)) ^ n ≤ (n.factorial : ℝ) * Real.exp (s ^ 2 / (8 * θ)) := by
    have := (div_le_iff₀ hfac).mp h1
    linarith
  have h3' : 8 * θ * (s ^ 2 / (8 * θ)) = s ^ 2 := by field_simp
  have h3 : s ^ (2 * n) = (8 * θ) ^ n * (s ^ 2 / (8 * θ)) ^ n := by
    rw [← mul_pow, h3', pow_mul]
  have h2 : s ^ (2 * n) ≤ (n.factorial : ℝ) * (8 * θ) ^ n * Real.exp (s ^ 2 / (8 * θ)) := by
    rw [h3]
    calc (8 * θ) ^ n * (s ^ 2 / (8 * θ)) ^ n
        ≤ (8 * θ) ^ n * ((n.factorial : ℝ) * Real.exp (s ^ 2 / (8 * θ))) :=
          mul_le_mul_of_nonneg_left h4 (pow_nonneg h8.le n)
      _ = (n.factorial : ℝ) * (8 * θ) ^ n * Real.exp (s ^ 2 / (8 * θ)) := by ring
  have hK : 0 ≤ (Real.sqrt (4 * Real.pi * θ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h5 : Real.exp (s ^ 2 / (8 * θ)) * Real.exp (-(1 / (4 * θ)) * s ^ 2)
      = Real.exp (-(1 / (8 * θ)) * s ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [adjSD_g_eq]
  calc s ^ (2 * n) * ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (4 * θ)) * s ^ 2))
      ≤ ((n.factorial : ℝ) * (8 * θ) ^ n * Real.exp (s ^ 2 / (8 * θ)))
          * ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (4 * θ)) * s ^ 2)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hK (Real.exp_pos _).le)
    _ = ((n.factorial : ℝ) * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
          * (Real.exp (s ^ 2 / (8 * θ)) * Real.exp (-(1 / (4 * θ)) * s ^ 2)) := by ring
    _ = ((n.factorial : ℝ) * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
          * Real.exp (-(1 / (8 * θ)) * s ^ 2) := by rw [h5]

/-- The weighted Gaussian moment is integrable. -/
theorem adjSD_integrable_moment {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    Integrable (fun s : ℝ => s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s) := by
  have h8 : (0:ℝ) < 8 * θ := by linarith
  have hb : (0:ℝ) < 1 / (8 * θ) := div_pos one_pos h8
  have hI := (integrable_exp_neg_mul_sq hb).const_mul
    (n.factorial * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
  refine hI.mono' ?_ ?_
  · exact ((continuous_pow (2 * n)).mul
      (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).continuous).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    have hnn : 0 ≤ s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s :=
      mul_nonneg (by rw [pow_mul]; positivity)
        (UnforcedLeray.B0191.heatKernel_pos one_pos hθ s).le
    rw [Real.norm_of_nonneg hnn]
    exact adjSD_moment_pointwise hθ n s

/-- The Gaussian moment bound `∫ s^{2n} G_θ(s) ds ≤ 2 n! (8θ)^n`. -/
theorem adjSD_integral_moment_le {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ∫ s : ℝ, s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s
      ≤ 2 * ((n.factorial : ℝ) * (8 * θ) ^ n) := by
  have h8 : (0:ℝ) < 8 * θ := by linarith
  have hb : (0:ℝ) < 1 / (8 * θ) := div_pos one_pos h8
  have hI := (integrable_exp_neg_mul_sq hb).const_mul
    (n.factorial * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
  have hpos4 : 0 < 4 * Real.pi * θ := mul_pos (mul_pos (by norm_num) Real.pi_pos) hθ
  have hb0 : 0 < Real.sqrt (4 * Real.pi * θ) := Real.sqrt_pos.mpr hpos4
  have hsq : Real.sqrt (8 * Real.pi * θ) ≤ 2 * Real.sqrt (4 * Real.pi * θ) := by
    calc Real.sqrt (8 * Real.pi * θ) ≤ Real.sqrt ((2 * Real.sqrt (4 * Real.pi * θ)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [mul_pow, Real.sq_sqrt hpos4.le]
          nlinarith [mul_pos Real.pi_pos hθ]
      _ = 2 * Real.sqrt (4 * Real.pi * θ) := Real.sqrt_sq (by positivity)
  have hbinv : (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.sqrt (8 * Real.pi * θ) ≤ 2 := by
    rw [inv_mul_le_iff₀ hb0]
    linarith
  have hπ : Real.pi / (1 / (8 * θ)) = 8 * Real.pi * θ := by
    rw [div_div_eq_mul_div, div_one]
    ring
  have hnn : 0 ≤ (n.factorial : ℝ) * (8 * θ) ^ n :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h8.le n)
  calc ∫ s : ℝ, s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s
      ≤ ∫ s : ℝ, (n.factorial * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
          * Real.exp (-(1 / (8 * θ)) * s ^ 2) :=
        integral_mono (adjSD_integrable_moment hθ n) hI
          (fun s => adjSD_moment_pointwise hθ n s)
    _ = (n.factorial * (8 * θ) ^ n * (Real.sqrt (4 * Real.pi * θ))⁻¹)
          * Real.sqrt (Real.pi / (1 / (8 * θ))) := by
        rw [integral_const_mul, integral_gaussian]
    _ = ((n.factorial : ℝ) * (8 * θ) ^ n)
          * ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.sqrt (8 * Real.pi * θ)) := by
        rw [hπ]
        ring
    _ ≤ ((n.factorial : ℝ) * (8 * θ) ^ n) * 2 := mul_le_mul_of_nonneg_left hbinv hnn
    _ = 2 * ((n.factorial : ℝ) * (8 * θ) ^ n) := by ring

/-- The lift of the Gaussian moment to the plane: the function-level identity. -/
theorem adjSD_lift_fun (θ : ℝ) (n : ℕ) :
    (fun w : ℝ × ℝ => heatKernel2 θ w * w.2 ^ (2 * n))
      = fun w : ℝ × ℝ => UnforcedLeray.B0191.heatKernel 1 θ w.1
          * (w.2 ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ w.2) := by
  funext w
  simp only [UnforcedLeray.B0284.heatKernel2]
  ring

theorem adjSD_lift_integrable {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    Integrable (fun w : ℝ × ℝ => heatKernel2 θ w * w.2 ^ (2 * n)) := by
  have hg1 : Integrable (fun s : ℝ => UnforcedLeray.B0191.heatKernel 1 θ s) := by
    simpa using adjSD_integrable_moment hθ 0
  rw [adjSD_lift_fun θ n]
  exact Integrable.mul_prod hg1 (adjSD_integrable_moment hθ n)

theorem adjSD_lift_bound {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ∫ w : ℝ × ℝ, heatKernel2 θ w * w.2 ^ (2 * n)
      ≤ 2 * ((n.factorial : ℝ) * (8 * θ) ^ n) := by
  have key : ∫ w : ℝ × ℝ, heatKernel2 θ w * w.2 ^ (2 * n)
      = (∫ s : ℝ, UnforcedLeray.B0191.heatKernel 1 θ s)
        * ∫ s : ℝ, s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s := by
    rw [adjSD_lift_fun θ n]
    exact integral_prod_mul (fun s : ℝ => UnforcedLeray.B0191.heatKernel 1 θ s)
      (fun s : ℝ => s ^ (2 * n) * UnforcedLeray.B0191.heatKernel 1 θ s)
  rw [key, UnforcedLeray.B0284.integral_heatKernel_one hθ, one_mul]
  exact adjSD_integral_moment_le hθ n

/-- **Rapid `η`-decay of the smoothed tests, uniform in `θ ∈ [0, Θ]`** (SP 2819-2836). -/
theorem adjSmoothDecay : AdjSmoothDecay := by
  unfold AdjSmoothDecay
  intro c hc ψ hψ Θ k hΘ hk
  obtain ⟨M, hM0, hM⟩ := Exist.cylTest_exists_bound hc hψ
  obtain ⟨R0, hR0⟩ := hψ.band
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = |R0| + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    linarith [abs_nonneg R0]
  obtain ⟨n, hn⟩ := exists_nat_ge k
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * ((n.factorial : ℝ) * (8 * Θ) ^ n) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) n))
  have hCfar0 : 0 ≤ M * 2 ^ (2 * n) * K * 2 ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg hM0 (by positivity)) hK0) (by positivity)
  have hCmid0 : 0 ≤ M * (1 + (2 * A) ^ 2) ^ k := mul_nonneg hM0 (by positivity)
  have hMK : 0 ≤ M * 2 ^ (2 * n) * K := mul_nonneg (mul_nonneg hM0 (by positivity)) hK0
  refine ⟨M * 2 ^ (2 * n) * K * 2 ^ k + M * (1 + (2 * A) ^ 2) ^ k, fun θ hθ x => ?_⟩
  have hC0 : 0 ≤ M * 2 ^ (2 * n) * K * 2 ^ k + M * (1 + (2 * A) ^ 2) ^ k :=
    add_nonneg hCfar0 hCmid0
  have hXnn : 0 ≤ (1 + x.2 ^ 2) ^ (-k) :=
    Real.rpow_nonneg (show (0:ℝ) ≤ 1 + x.2 ^ 2 by positivity) _
  by_cases hy : 2 * A ≤ |x.2|
  · -- far region: `|η| ≥ 2A`
    have hy1 : 1 ≤ |x.2| := by linarith
    have hy2 : 1 ≤ x.2 ^ 2 := by
      have : 1 ≤ |x.2| ^ 2 := by nlinarith
      rwa [sq_abs] at this
    have hlt : R0 < |x.2| := by linarith [le_abs_self R0, abs_nonneg R0]
    by_cases hθ0 : 0 < θ
    · obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = |x.2| / 2 := ⟨_, rfl⟩
      have ht : 0 < t := by
        rw [ht_def]
        linarith
      have hQ : 0 < (x.2 ^ 2) ^ n := pow_pos (by linarith) n
      have hP : 0 < (1 + x.2 ^ 2) ^ k := Real.rpow_pos_of_pos (by positivity) k
      have hpow_abs : |x.2| ^ (2 * n) = (x.2 ^ 2) ^ n := by
        rw [pow_mul, sq_abs]
      have ht2 : t ^ (2 * n) = (x.2 ^ 2) ^ n / 2 ^ (2 * n) := by
        rw [ht_def, div_pow, hpow_abs]
      have hkey : (1 + x.2 ^ 2) ^ k ≤ 2 ^ k * (x.2 ^ 2) ^ n := by
        have h1 : 1 + x.2 ^ 2 ≤ 2 * x.2 ^ 2 := by linarith
        have h2 : (1 + x.2 ^ 2) ^ k ≤ (2 * x.2 ^ 2) ^ k :=
          Real.rpow_le_rpow (by positivity) h1 hk
        have h3 : (2 * x.2 ^ 2) ^ k = 2 ^ k * (x.2 ^ 2) ^ k :=
          Real.mul_rpow (by norm_num) (by positivity)
        have h4 : (x.2 ^ 2) ^ k ≤ (x.2 ^ 2) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy2 hn
        rw [Real.rpow_natCast] at h4
        calc (1 + x.2 ^ 2) ^ k ≤ (2 * x.2 ^ 2) ^ k := h2
          _ = 2 ^ k * (x.2 ^ 2) ^ k := h3
          _ ≤ 2 ^ k * (x.2 ^ 2) ^ n := mul_le_mul_of_nonneg_left h4 (by positivity)
      have hpt : ∀ w : ℝ × ℝ, |heatKernel2 θ w * ψ (x - w)|
          ≤ (M / t ^ (2 * n)) * (heatKernel2 θ w * w.2 ^ (2 * n)) := by
        intro w
        have hg0 : 0 ≤ heatKernel2 θ w := UnforcedLeray.B0284.heatKernel2_nonneg hθ0 w
        have hw2 : 0 ≤ w.2 ^ (2 * n) := by
          rw [pow_mul]
          positivity
        have hR : 0 ≤ M / t ^ (2 * n) := div_nonneg hM0 (pow_nonneg ht.le _)
        have hRHS : 0 ≤ heatKernel2 θ w * w.2 ^ (2 * n) := mul_nonneg hg0 hw2
        by_cases hw : |w.2| < t
        · have hz : R0 < |(x - w).2| := by
            rw [Prod.snd_sub]
            linarith [abs_sub_abs_le_abs_sub x.2 w.2, le_abs_self R0, abs_nonneg R0]
          rw [hR0 (x - w) hz, mul_zero, abs_zero]
          exact mul_nonneg hR hRHS
        · push_neg at hw
          have hpow : t ^ (2 * n) ≤ w.2 ^ (2 * n) := by
            have h := pow_le_pow_left₀ ht.le hw (2 * n)
            rwa [Even.pow_abs ⟨n, two_mul n⟩] at h
          have hq : 1 ≤ w.2 ^ (2 * n) / t ^ (2 * n) := (one_le_div (pow_pos ht _)).mpr hpow
          have hGM : 0 ≤ heatKernel2 θ w * M := mul_nonneg hg0 hM0
          calc |heatKernel2 θ w * ψ (x - w)| = heatKernel2 θ w * |ψ (x - w)| := by
                rw [abs_mul, abs_of_nonneg hg0]
            _ ≤ heatKernel2 θ w * M := mul_le_mul_of_nonneg_left (hM (x - w)) hg0
            _ ≤ heatKernel2 θ w * M * (w.2 ^ (2 * n) / t ^ (2 * n)) :=
                le_mul_of_one_le_right hGM hq
            _ = (M / t ^ (2 * n)) * (heatKernel2 θ w * w.2 ^ (2 * n)) := by ring
      have hint : Integrable
          (fun w : ℝ × ℝ => (M / t ^ (2 * n)) * (heatKernel2 θ w * w.2 ^ (2 * n))) :=
        (adjSD_lift_integrable hθ0 n).const_mul _
      have hbound : ∫ w : ℝ × ℝ, heatKernel2 θ w * w.2 ^ (2 * n) ≤ K := by
        refine (adjSD_lift_bound hθ0 n).trans ?_
        rw [hKdef]
        have h8 : 8 * θ ≤ 8 * Θ := by linarith [hθ.2]
        have hp : (8 * θ) ^ n ≤ (8 * Θ) ^ n := pow_le_pow_left₀ (by linarith) h8 n
        have hnn : (0:ℝ) ≤ n.factorial := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hnn) (by norm_num)
      have hfar : |Exist.cylHeatSmooth c θ ψ x| ≤ (M / t ^ (2 * n)) * K := by
        rw [Exist.cylHeatSmooth_apply_of_pos hθ0 ψ x, ← Real.norm_eq_abs]
        calc ‖∫ w : ℝ × ℝ, heatKernel2 θ w * ψ (x - w)‖
            ≤ ∫ w : ℝ × ℝ, (M / t ^ (2 * n)) * (heatKernel2 θ w * w.2 ^ (2 * n)) :=
              MeasureTheory.norm_integral_le_of_norm_le hint
                (Eventually.of_forall fun w => by
                  rw [Real.norm_eq_abs]
                  exact hpt w)
          _ = (M / t ^ (2 * n)) * ∫ w : ℝ × ℝ, heatKernel2 θ w * w.2 ^ (2 * n) :=
              integral_const_mul _ _
          _ ≤ (M / t ^ (2 * n)) * K :=
              mul_le_mul_of_nonneg_left hbound (div_nonneg hM0 (pow_nonneg ht.le _))
      have e1 : M / t ^ (2 * n) * K = (M * 2 ^ (2 * n) * K) * ((x.2 ^ 2) ^ n)⁻¹ := by
        rw [ht2, div_div_eq_mul_div]
        ring
      have hinv : ((x.2 ^ 2) ^ n)⁻¹ ≤ 2 ^ k * ((1 + x.2 ^ 2) ^ k)⁻¹ := by
        calc ((x.2 ^ 2) ^ n)⁻¹ = 1 / (x.2 ^ 2) ^ n := by ring
          _ ≤ 2 ^ k / (1 + x.2 ^ 2) ^ k := by
              rw [div_le_div_iff₀ hQ hP]
              linarith [hkey]
          _ = 2 ^ k * ((1 + x.2 ^ 2) ^ k)⁻¹ := by ring
      calc |Exist.cylHeatSmooth c θ ψ x| ≤ (M / t ^ (2 * n)) * K := hfar
        _ = (M * 2 ^ (2 * n) * K) * ((x.2 ^ 2) ^ n)⁻¹ := e1
        _ ≤ (M * 2 ^ (2 * n) * K) * (2 ^ k * ((1 + x.2 ^ 2) ^ k)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv hMK
        _ = (M * 2 ^ (2 * n) * K * 2 ^ k) * ((1 + x.2 ^ 2) ^ k)⁻¹ := by ring
        _ = (M * 2 ^ (2 * n) * K * 2 ^ k) * (1 + x.2 ^ 2) ^ (-k) := by
            rw [Real.rpow_neg (show (0:ℝ) ≤ 1 + x.2 ^ 2 by positivity)]
        _ ≤ (M * 2 ^ (2 * n) * K * 2 ^ k + M * (1 + (2 * A) ^ 2) ^ k) * (1 + x.2 ^ 2) ^ (-k) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCmid0) hXnn
    · -- `θ = 0`: `P_0 ψ = ψ`, which vanishes for `|η| > R`
      have hθ' : θ ≤ 0 := not_lt.mp hθ0
      rw [Exist.cylHeatSmooth_of_nonpos hθ' ψ, hR0 x hlt, abs_zero]
      exact mul_nonneg hC0 hXnn
  · -- middle region: `|η| < 2A`, use the sup bound
    push_neg at hy
    have hmid : |Exist.cylHeatSmooth c θ ψ x| ≤ M := Exist.abs_cylHeatSmooth_le hM x
    have hsq : x.2 ^ 2 ≤ (2 * A) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg x.2) hy.le 2
      rwa [sq_abs] at h
    have hP : (1 + x.2 ^ 2) ^ k ≤ (1 + (2 * A) ^ 2) ^ k :=
      Real.rpow_le_rpow (by positivity) (by linarith) hk
    have hPpos : 0 < (1 + x.2 ^ 2) ^ k := Real.rpow_pos_of_pos (by positivity) k
    have hq : 1 ≤ (1 + (2 * A) ^ 2) ^ k * ((1 + x.2 ^ 2) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hPpos]
      exact hP
    have h1 : M ≤ M * (1 + (2 * A) ^ 2) ^ k * (1 + x.2 ^ 2) ^ (-k) := by
      rw [Real.rpow_neg (show (0:ℝ) ≤ 1 + x.2 ^ 2 by positivity)]
      calc M = M * 1 := (mul_one M).symm
        _ ≤ M * ((1 + (2 * A) ^ 2) ^ k * ((1 + x.2 ^ 2) ^ k)⁻¹) :=
            mul_le_mul_of_nonneg_left hq hM0
        _ = M * (1 + (2 * A) ^ 2) ^ k * ((1 + x.2 ^ 2) ^ k)⁻¹ := by ring
    calc |Exist.cylHeatSmooth c θ ψ x| ≤ M := hmid
      _ ≤ M * (1 + (2 * A) ^ 2) ^ k * (1 + x.2 ^ 2) ^ (-k) := h1
      _ ≤ (M * 2 ^ (2 * n) * K * 2 ^ k + M * (1 + (2 * A) ^ 2) ^ k) * (1 + x.2 ^ 2) ^ (-k) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCfar0) hXnn

end UnforcedLeray.Short.IIIa
