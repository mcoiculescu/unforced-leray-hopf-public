import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Matrix

namespace UnforcedLeray.Short.IIIa

/-- `PartIII-a:T21/2/7/2/1/1/2/18`: the finite-difference estimate (`Interp1DFD`). -/
theorem interp1DFD : Interp1DFD := by
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- Vandermonde weights for the nodes 0, 1, ..., n
  have hinj : Function.Injective (fun i : Fin (n + 1) => ((i : ℕ) : ℝ)) := by
    intro i j hij
    have hij' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := hij
    apply Fin.ext
    exact_mod_cast hij'
  have hunit : IsUnit
      ((Matrix.vandermonde (fun i : Fin (n + 1) => ((i : ℕ) : ℝ))).transpose).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hinj)
  obtain ⟨w, hw⟩ : ∃ w : Fin (n + 1) → ℝ, ∀ k : ℕ, k < n + 1 →
      ∑ i, w i * ((i : ℕ) : ℝ) ^ k = if k = 1 then 1 else 0 := by
    set A := (Matrix.vandermonde (fun i : Fin (n + 1) => ((i : ℕ) : ℝ))).transpose with hA
    set e : Fin (n + 1) → ℝ := Pi.single (⟨1, by omega⟩ : Fin (n + 1)) 1 with he
    have hmv : A *ᵥ (A⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    generalize A⁻¹ *ᵥ e = u at hmv
    refine ⟨u, fun k hk => ?_⟩
    have hc := congrFun hmv ⟨k, hk⟩
    simp only [hA, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde,
      Matrix.of_apply, he, Pi.single_apply, Fin.mk.injEq] at hc
    rw [← hc]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  obtain ⟨W0, hW0⟩ : ∃ W0 : ℝ, W0 = ∑ i, |w i| := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) := ⟨_, rfl⟩
  have hW0nn : 0 ≤ W0 := by
    rw [hW0]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hKnn : 0 ≤ K := by
    rw [hK]
    positivity
  refine ⟨W0 + W0 * K, add_nonneg hW0nn (mul_nonneg hW0nn hKnn), ?_⟩
  intro g t₀ A M hg hA hM h hh0 hh1
  have hab : t₀ < t₀ + 1 := by linarith
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA t₀ ⟨le_rfl, by linarith⟩)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t₀ ⟨le_rfl, by linarith⟩)
  have hNh : h * ((n : ℝ) + 1) ≤ 1 := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h' : h ≤ 1 / ((n : ℝ) + 1) := by
      push_cast at hh1
      exact hh1
    exact (le_div_iff₀ hpos).1 h'
  have hiR : ∀ i : Fin (n + 1), ((i : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    intro i
    have : (i : ℕ) ≤ n + 1 := i.isLt.le
    exact_mod_cast this
  -- the nodes lie in the unit interval
  have hxmem : ∀ i : Fin (n + 1), t₀ + ((i : ℕ) : ℝ) * h ∈ Icc t₀ (t₀ + 1) := by
    intro i
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : ((i : ℕ) : ℝ) * h ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.2 (hiR i)) hh0.le]
    exact ⟨by nlinarith [mul_nonneg hi0 hh0.le], by linarith⟩
  -- Taylor expansion at each node
  have hTay : ∀ i : Fin (n + 1), |g (t₀ + ((i : ℕ) : ℝ) * h) -
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (((i : ℕ) : ℝ) * h) ^ k) *
        iteratedDeriv k g t₀| ≤
      M * ((((i : ℕ) : ℝ) * h) ^ (n + 1)) / (n.factorial : ℝ) := by
    intro i
    have hcont : ∀ k : ℕ, k ≤ n + 1 → ContDiffAt ℝ k g t₀ := fun k hk =>
      hg.contDiffAt.of_le (by exact_mod_cast hk)
    have hC : ∀ y ∈ Icc t₀ (t₀ + 1), ‖iteratedDerivWithin (n + 1) g (Icc t₀ (t₀ + 1)) y‖ ≤ M := by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hg.contDiffAt hy,
        Real.norm_eq_abs]
      exact hM y hy
    have hb := taylor_mean_remainder_bound (f := g) (x := t₀ + ((i : ℕ) : ℝ) * h) hab.le
      hg.contDiffOn (hxmem i) hC
    have hs : taylorWithinEval g n (Icc t₀ (t₀ + 1)) t₀ (t₀ + ((i : ℕ) : ℝ) * h) =
        ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (((i : ℕ) : ℝ) * h) ^ k) *
          iteratedDeriv k g t₀ := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ n + 1 := by
        have := Finset.mem_range.1 hk
        omega
      rw [smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
        (hcont k hk') (left_mem_Icc.2 hab.le), add_sub_cancel_left]
    rw [hs, Real.norm_eq_abs, add_sub_cancel_left] at hb
    exact hb
  obtain ⟨P, hP⟩ : ∃ P : Fin (n + 1) → ℝ, ∀ i, P i =
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (((i : ℕ) : ℝ) * h) ^ k) *
        iteratedDeriv k g t₀ :=
    ⟨fun i => ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (((i : ℕ) : ℝ) * h) ^ k) *
        iteratedDeriv k g t₀, fun i => rfl⟩
  -- the remainders
  have hR : ∀ i : Fin (n + 1), |g (t₀ + ((i : ℕ) : ℝ) * h) - P i| ≤ M * K * h ^ (n + 1) := by
    intro i
    rw [hP]
    refine (hTay i).trans ?_
    have hpow : (((i : ℕ) : ℝ) * h) ^ (n + 1) ≤ ((n : ℝ) + 1) ^ (n + 1) * h ^ (n + 1) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (hiR i) (n + 1))
        (pow_nonneg hh0.le _)
    have hMK : M * (((i : ℕ) : ℝ) * h) ^ (n + 1) / (n.factorial : ℝ) ≤
        M * (((n : ℝ) + 1) ^ (n + 1) * h ^ (n + 1)) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hM0) (by positivity)
    rw [hK]
    calc M * (((i : ℕ) : ℝ) * h) ^ (n + 1) / (n.factorial : ℝ)
        ≤ M * (((n : ℝ) + 1) ^ (n + 1) * h ^ (n + 1)) / (n.factorial : ℝ) := hMK
      _ = M * (((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ)) * h ^ (n + 1) := by ring
  -- the weighted sum of the Taylor polynomials is h g'(t₀)
  have halg : ∑ i, w i * P i = h * iteratedDeriv 1 g t₀ := by
    simp only [hP]
    calc ∑ i, w i * (∑ k ∈ Finset.range (n + 1),
          ((k.factorial : ℝ)⁻¹ * (((i : ℕ) : ℝ) * h) ^ k) * iteratedDeriv k g t₀)
        = ∑ i, ∑ k ∈ Finset.range (n + 1),
            (w i * ((i : ℕ) : ℝ) ^ k) * ((k.factorial : ℝ)⁻¹ * h ^ k) * iteratedDeriv k g t₀ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [mul_pow]
          ring
      _ = ∑ k ∈ Finset.range (n + 1),
            (∑ i, w i * ((i : ℕ) : ℝ) ^ k) * ((k.factorial : ℝ)⁻¹ * h ^ k) *
              iteratedDeriv k g t₀ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = ∑ k ∈ Finset.range (n + 1),
            (if k = 1 then ((k.factorial : ℝ)⁻¹ * h ^ k) * iteratedDeriv k g t₀ else 0) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [hw k (Finset.mem_range.1 hk)]
          split_ifs <;> simp
      _ = h * iteratedDeriv 1 g t₀ := by
          have h1mem : (1 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
          rw [Finset.sum_ite_eq', if_pos h1mem]
          simp
  have hsplit : ∑ i, w i * g (t₀ + ((i : ℕ) : ℝ) * h) =
      h * iteratedDeriv 1 g t₀ + ∑ i, w i * (g (t₀ + ((i : ℕ) : ℝ) * h) - P i) := by
    rw [← halg, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- the bounds on the two sums
  have hS : |∑ i, w i * g (t₀ + ((i : ℕ) : ℝ) * h)| ≤ W0 * A := by
    rw [hW0, Finset.sum_mul]
    calc |∑ i, w i * g (t₀ + ((i : ℕ) : ℝ) * h)|
        ≤ ∑ i, |w i * g (t₀ + ((i : ℕ) : ℝ) * h)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * |g (t₀ + ((i : ℕ) : ℝ) * h)| := by simp only [abs_mul]
      _ ≤ ∑ i, |w i| * A := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hA _ (hxmem i)) (abs_nonneg _))
  have hE : |∑ i, w i * (g (t₀ + ((i : ℕ) : ℝ) * h) - P i)| ≤ W0 * (M * K * h ^ (n + 1)) := by
    rw [hW0, Finset.sum_mul]
    calc |∑ i, w i * (g (t₀ + ((i : ℕ) : ℝ) * h) - P i)|
        ≤ ∑ i, |w i * (g (t₀ + ((i : ℕ) : ℝ) * h) - P i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * |g (t₀ + ((i : ℕ) : ℝ) * h) - P i| := by simp only [abs_mul]
      _ ≤ ∑ i, |w i| * (M * K * h ^ (n + 1)) := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hR i) (abs_nonneg _))
  have hT : |h * iteratedDeriv 1 g t₀| ≤ W0 * A + W0 * (M * K * h ^ (n + 1)) := by
    have hd : h * iteratedDeriv 1 g t₀ = (∑ i, w i * g (t₀ + ((i : ℕ) : ℝ) * h)) -
        ∑ i, w i * (g (t₀ + ((i : ℕ) : ℝ) * h) - P i) := by
      linarith [hsplit]
    have h1 := abs_sub (∑ i, w i * g (t₀ + ((i : ℕ) : ℝ) * h))
      (∑ i, w i * (g (t₀ + ((i : ℕ) : ℝ) * h) - P i))
    rw [← hd] at h1
    linarith [hS, hE, h1]
  rw [abs_mul, abs_of_pos hh0, iteratedDeriv_one] at hT
  have hd1 : |deriv g t₀| ≤ W0 * (A / h) + W0 * K * (M * h ^ n) := by
    have h2 : |deriv g t₀| ≤ (W0 * A + W0 * (M * K * h ^ (n + 1))) / h := by
      rw [le_div_iff₀ hh0]
      linarith
    have h3 : (W0 * A + W0 * (M * K * h ^ (n + 1))) / h =
        W0 * (A / h) + W0 * K * (M * h ^ n) := by
      rw [pow_succ]
      field_simp
    linarith [h2, h3]
  rw [Nat.add_sub_cancel]
  have hA' : 0 ≤ A / h := div_nonneg hA0 hh0.le
  have hMh : 0 ≤ M * h ^ n := mul_nonneg hM0 (pow_nonneg hh0.le _)
  nlinarith [mul_nonneg hW0nn hMh, mul_nonneg (mul_nonneg hW0nn hKnn) hA']

end UnforcedLeray.Short.IIIa
