import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.Interp1DFD
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# `PartIII-a:T21/2/7/2/1/1/2/15`: the Landau-Kolmogorov interpolation on a unit interval

Proof of `Interp1D` (`Sub/AdjInterior/Train/Defs.lean`) from `interp1DFD`
(`Interp1DFD.lean`, the finite-difference estimate `|g'(t₀)| ≤ W (A/h + M h^{N-1})`).

* `N = 1`: `|g'(t₀)| ≤ M` directly.
* `N ≥ 2`, `A = 0`: the finite-difference bound reads `|g'(t₀)| ≤ W M h^{N-1}`; letting `h → 0⁺`
  gives `g'(t₀) = 0`.
* `N ≥ 2`, `A > 0`, `M ≤ A N^N`: `h = 1/N` gives `|g'(t₀)| ≤ 2 W N A`.
* `N ≥ 2`, `A > 0`, `M > A N^N`: `h = (A/M)^{1/N}` satisfies `h^N = A/M`, so `M h^{N-1} = A/h`
  and `A/h = A^{1-1/N} M^{1/N}`; this gives `|g'(t₀)| ≤ 2 W A^{1-1/N} M^{1/N}`.

The constant is `K = 2 W N`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem interp1D : Interp1D := by
  intro N hN
  rcases Nat.lt_or_ge N 2 with h2 | h2
  · -- the case `N = 1`
    have hN1 : N = 1 := by omega
    subst hN1
    refine ⟨1, zero_le_one, ?_⟩
    intro g t₀ A M hg hA hM
    have hd : |deriv g t₀| ≤ M := by
      have := hM t₀ ⟨le_refl _, by linarith⟩
      rwa [iteratedDeriv_one] at this
    have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA t₀ ⟨le_refl _, by linarith⟩)
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hd
    norm_num
    linarith
  · obtain ⟨W, hW0, hW⟩ := interp1DFD N h2
    refine ⟨2 * W * N, ?_, ?_⟩
    · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast h2
      exact mul_nonneg (mul_nonneg (by norm_num) hW0) (by linarith)
    intro g t₀ A M hg hA hM
    have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA t₀ ⟨le_refl _, by linarith⟩)
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM t₀ ⟨le_refl _, by linarith⟩)
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast h2
    have hNpos : (0 : ℝ) < N := by linarith
    have hNnn : (0 : ℝ) ≤ N := hNpos.le
    have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
    have hK : 0 ≤ 2 * W * N := mul_nonneg (mul_nonneg (by norm_num) hW0) hNnn
    have hder : ∀ h : ℝ, 0 < h → h ≤ 1 / (N : ℝ) →
        |deriv g t₀| ≤ W * (A / h + M * h ^ (N - 1)) :=
      fun h h0 h1 => hW g t₀ A M hg hA hM h h0 h1
    have hRnn : 0 ≤ A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hM0 _)
    rcases hA0.eq_or_lt with hAz | hApos
    · -- the case `A = 0`: the derivative vanishes
      subst hAz
      have hexp : (1 - 1 / (N : ℝ)) ≠ 0 := by
        have : 1 / (N : ℝ) < 1 := by
          rw [div_lt_one hNpos]; linarith
        linarith
      have hlim : Tendsto (fun h : ℝ => W * (M * h ^ (N - 1))) (𝓝[>] 0) (𝓝 0) := by
        have hc : Tendsto (fun h : ℝ => W * (M * h ^ (N - 1))) (𝓝 0)
            (𝓝 (W * (M * (0 : ℝ) ^ (N - 1)))) :=
          ((continuous_const.mul (continuous_const.mul (continuous_pow (N - 1)))).tendsto 0)
        have h0 : W * (M * (0 : ℝ) ^ (N - 1)) = 0 := by
          rw [zero_pow (by omega : N - 1 ≠ 0)]; ring
        rw [h0] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      have hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), |deriv g t₀| ≤ W * (M * h ^ (N - 1)) := by
        filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (N : ℝ))] with h hh
        have := hder h hh.1 hh.2.le
        simpa using this
      have hz : |deriv g t₀| ≤ 0 := ge_of_tendsto hlim hbound
      rw [Real.zero_rpow hexp, zero_mul, zero_add, mul_zero]
      exact hz
    · rcases le_or_gt M (A * (N : ℝ) ^ N) with hc1 | hc2
      · -- the case `M ≤ A N^N`: take `h = 1/N`
        have hdiv : A / (1 / (N : ℝ)) = A * N := by field_simp
        have key1 : M * (1 / (N : ℝ)) ^ (N - 1) ≤ A * N := by
          have hpow : (N : ℝ) ^ N = (N : ℝ) ^ (N - 1) * N := by
            rw [← pow_succ]; congr 1; omega
          have hpos : (0 : ℝ) < (N : ℝ) ^ (N - 1) := pow_pos hNpos _
          rw [one_div_pow, mul_one_div, div_le_iff₀ hpos]
          calc M ≤ A * (N : ℝ) ^ N := hc1
            _ = A * N * (N : ℝ) ^ (N - 1) := by rw [hpow]; ring
        have hstep := hder (1 / (N : ℝ)) (by positivity) le_rfl
        calc |deriv g t₀| ≤ W * (A / (1 / (N : ℝ)) + M * (1 / (N : ℝ)) ^ (N - 1)) := hstep
          _ ≤ W * (A * N + A * N) := by
              apply mul_le_mul_of_nonneg_left _ hW0
              rw [hdiv]; linarith [key1]
          _ = 2 * W * N * A := by ring
          _ ≤ 2 * W * N * (A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ)) + A) :=
              mul_le_mul_of_nonneg_left (by linarith) hK
      · -- the case `M > A N^N`: take `h = (A/M)^{1/N}`
        have hMpos : 0 < M := by
          have : 0 < A * (N : ℝ) ^ N := by positivity
          linarith
        obtain ⟨h, hhdef⟩ : ∃ h : ℝ, h = (A / M) ^ (1 / (N : ℝ)) := ⟨_, rfl⟩
        have hh0 : 0 < h := by
          rw [hhdef]; exact Real.rpow_pos_of_pos (div_pos hApos hMpos) _
        have hhN : h ^ N = A / M := by
          rw [hhdef, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hA0 hM0),
            one_div_mul_cancel (ne_of_gt hNpos), Real.rpow_one]
        have hh1 : h ≤ 1 / (N : ℝ) := by
          have hpowle : h ^ N ≤ (1 / (N : ℝ)) ^ N := by
            rw [hhN, one_div_pow, div_le_div_iff₀ hMpos (pow_pos hNpos N)]
            linarith
          exact le_of_pow_le_pow_left₀ (by omega : N ≠ 0) (by positivity) hpowle
        have hMh : M * h ^ (N - 1) = A / h := by
          have hsplit : h ^ N = h ^ (N - 1) * h := by
            rw [← pow_succ]; congr 1; omega
          rw [eq_div_iff hh0.ne']
          calc M * h ^ (N - 1) * h = M * (h ^ (N - 1) * h) := by ring
            _ = M * h ^ N := by rw [hsplit]
            _ = A := by rw [hhN]; field_simp
        have hAeq : A / h = A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ)) := by
          rw [hhdef, Real.div_rpow hA0 hM0, Real.rpow_sub hApos, Real.rpow_one,
            div_div_eq_mul_div]
          ring
        have hstep := hder h hh0 hh1
        rw [hMh, hAeq] at hstep
        have hR := hRnn
        calc |deriv g t₀| ≤ W * (A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ)) +
              A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ))) := hstep
          _ = 2 * W * (A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ))) := by ring
          _ ≤ 2 * W * N * (A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ)) + A) := by
              nlinarith [mul_nonneg (mul_nonneg hW0 hN1) hR,
                mul_nonneg (mul_nonneg hW0 hNnn) hA0]

end UnforcedLeray.Short.IIIa
