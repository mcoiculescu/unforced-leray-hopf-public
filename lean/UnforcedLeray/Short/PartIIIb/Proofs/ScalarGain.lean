import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `T_scalarGain` (source: `the November 2 reference manuscript`, lines 5960-5972)

Assume `T_unitRespExact` and `T_mellinContinuousAt`. On the phase-locked sequence, for all large
`n`, the exact identity gives `unitResp = e^{-z} Re(𝒞(μ_n(z))/𝒞(σ₀))` with
`μ_n(z) = σ₀ + z/(2|log ν_n|)`. The window `μ_n(z)` tends to `σ₀` uniformly on `[-1,1]`, and
`𝒞` is continuous at `σ₀` with `𝒞(σ₀) ≠ 0`. Since `0 < e^{-z} ≤ e` on `[-1,1]` and
`|Re w| ≤ ‖w‖`, the difference `|e^{-z} Re r - e^{-z}|` is at most `e ‖r - 1‖`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

theorem scalarGain : UnforcedLeray.Short.PartIIIb.T_scalarGain := by
  unfold UnforcedLeray.Short.PartIIIb.T_scalarGain UnforcedLeray.Short.PartIIIb.ScalarGainLimit
  intro hExact hCont lam κ ell J σ₀ hlam hlamim hell hJc hσ hCne ν hνpos hνlim hphase
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hEne : Real.exp 1 ≠ 0 := hE.ne'
  -- continuity of the normalised Mellin quotient at σ₀
  have hgc : ContinuousAt (fun μ : ℂ => mellinC lam ell J μ / mellinC lam ell J (σ₀ : ℂ))
      (σ₀ : ℂ) :=
    (hCont lam ell J σ₀ hlam hσ hJc).div_const _
  obtain ⟨δ, hδ, hδball⟩ := Metric.continuousAt_iff.1 hgc (ε / Real.exp 1) (div_pos hε hE)
  -- eventually: ν n < 1, ν n < exp(-1/δ), and the phase is an integer multiple of 2π
  have hK : ∀ᶠ n : ℕ in atTop, ν n < Real.exp (-(1 / δ)) :=
    hνlim.eventually (gt_mem_nhds (Real.exp_pos _))
  have hν1 : ∀ᶠ n : ℕ in atTop, ν n < 1 :=
    hνlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hphase2 : ∀ᶠ n : ℕ in atTop, ∃ m : ℤ,
      lam.im / ν n - κ.im * Real.log (ν n) + Complex.arg (mellinC lam ell J (σ₀ : ℂ))
        = 2 * Real.pi * m := by
    refine hphase.mono fun n hn => ?_
    rcases lt_or_gt_of_ne hlamim with h | h
    · refine ⟨-(n : ℤ), ?_⟩
      rw [Real.sign_of_neg h] at hn
      push_cast
      linear_combination hn
    · refine ⟨(n : ℤ), ?_⟩
      rw [Real.sign_of_pos h] at hn
      push_cast
      linear_combination hn
  filter_upwards [hK, hν1, hphase2] with n hKn hν1n hphn
  intro z hz
  -- the exact identity (T_unitRespExact)
  have hT := hExact lam κ ell J σ₀ (ν n) z (hνpos n) hν1n hCne hphn
  rw [hT]
  -- |log ν_n| > 1/δ, hence |μ_n(z) - σ₀| < δ
  have hlog_lt : Real.log (ν n) < -(1 / δ) := by
    have h := Real.log_lt_log (hνpos n) hKn
    rwa [Real.log_exp] at h
  have hδinv : 0 < 1 / δ := one_div_pos.2 hδ
  have habs : |Real.log (ν n)| = -Real.log (ν n) := abs_of_neg (by linarith)
  have hLpos : 0 < |Real.log (ν n)| := by rw [habs]; linarith
  have hLδ : 1 < |Real.log (ν n)| * δ := by
    have h1 : 1 / δ < |Real.log (ν n)| := by rw [habs]; linarith
    exact (div_lt_iff₀ hδ).1 h1
  have hdist : dist ((muWin σ₀ (ν n) z : ℝ) : ℂ) (σ₀ : ℂ) < δ := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hmu : muWin σ₀ (ν n) z - σ₀ = z / (2 * |Real.log (ν n)|) := by
      unfold muWin
      ring
    rw [hmu, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * |Real.log (ν n)|),
      div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * |Real.log (ν n)|)]
    have hz1 : |z| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
    nlinarith [hz1, hLδ, hδ]
  -- the quotient is close to 1
  have hr : dist (mellinC lam ell J ((muWin σ₀ (ν n) z : ℝ) : ℂ) / mellinC lam ell J (σ₀ : ℂ))
      (mellinC lam ell J (σ₀ : ℂ) / mellinC lam ell J (σ₀ : ℂ)) < ε / Real.exp 1 :=
    hδball hdist
  rw [div_self hCne, dist_eq_norm] at hr
  -- the final bound
  have hexp_le : Real.exp (-z) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith [hz.1])
  have hexp_pos : 0 < Real.exp (-z) := Real.exp_pos _
  set r := mellinC lam ell J ((muWin σ₀ (ν n) z : ℝ) : ℂ) / mellinC lam ell J (σ₀ : ℂ) with hr_def
  have hre : |r.re - 1| ≤ ‖r - 1‖ := by
    have h : r.re - 1 = (r - 1).re := by simp
    rw [h]
    exact Complex.abs_re_le_norm _
  have hfinal : |Real.exp (-z) - Real.exp (-z) * r.re| = Real.exp (-z) * |r.re - 1| := by
    rw [show Real.exp (-z) - Real.exp (-z) * r.re = -(Real.exp (-z) * (r.re - 1)) by ring,
      abs_neg, abs_mul, abs_of_pos hexp_pos]
  rw [Real.dist_eq, hfinal]
  calc Real.exp (-z) * |r.re - 1| ≤ Real.exp 1 * |r.re - 1| :=
        mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
    _ ≤ Real.exp 1 * ‖r - 1‖ := mul_le_mul_of_nonneg_left hre hE.le
    _ < Real.exp 1 * (ε / Real.exp 1) := mul_lt_mul_of_pos_left hr hE
    _ = ε := by field_simp

end UnforcedLeray.Short.PartIIIb
