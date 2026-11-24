import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- Real directional derivative of a complex-differentiable map. -/
theorem decay_fderiv_holo (F : ℂ → ℂ) (F' z v : ℂ) (h : HasDerivAt F F' z) :
    fderiv ℝ F z v = F' * v := by
  have h2 := h.hasFDerivAt.restrictScalars ℝ
  rw [h2.fderiv]
  simp [mul_comm]

/-- Derivative of `c (w^n)⁻¹` in direction `v`, with its norm bound. -/
theorem decay_hasDeriv (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => c * (w ^ n)⁻¹) (c * (-((n : ℂ) * z ^ (n - 1)) / (z ^ n) ^ 2)) z :=
  ((hasDerivAt_pow n z).inv (pow_ne_zero n hz)).const_mul c

theorem decay_norm_holo (c : ℂ) (n : ℕ) (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    ‖c * (-((n : ℂ) * z ^ (n - 1)) / (z ^ n) ^ 2) * v‖ ≤ ‖c‖ * n * (‖z‖ ^ (n + 1))⁻¹ * ‖v‖ := by
  have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have e : ‖c * (-((n : ℂ) * z ^ (n - 1)) / (z ^ n) ^ 2)‖ = ‖c‖ * n * (‖z‖ ^ (n + 1))⁻¹ := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  rw [norm_mul, e]

/-- Conjugate version of the holomorphic derivative bound. -/
theorem decay_norm_conj (c : ℂ) (n : ℕ) (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    ‖fderiv ℝ (fun w : ℂ => (starRingEnd ℂ) (c * (w ^ n)⁻¹)) z v‖ ≤
      ‖c‖ * n * (‖z‖ ^ (n + 1))⁻¹ * ‖v‖ := by
  have hd := decay_hasDeriv c n hz
  have hH : HasFDerivAt (fun w : ℂ => c * (w ^ n)⁻¹)
      (fderiv ℝ (fun w : ℂ => c * (w ^ n)⁻¹) z) z :=
    (hd.differentiableAt.restrictScalars ℝ).hasFDerivAt
  have hc : (fun w : ℂ => (starRingEnd ℂ) (c * (w ^ n)⁻¹)) =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ (fun w : ℂ => c * (w ^ n)⁻¹) := by
    funext w
    simp
  have hcomp := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hH
  rw [hc, hcomp.fderiv, ContinuousLinearMap.comp_apply]
  rw [decay_fderiv_holo _ _ z v hd]
  have := decay_norm_holo c n hn hz v
  simpa [Complex.norm_conj] using this

/-- Global decay of the derivative from a pointwise bound. -/
theorem decay_tendsto (G : ℂ → ℂ) (n : ℕ) (K R : ℝ) (hK : 0 ≤ K)
    (hG : ∀ z : ℂ, R < ‖z‖ → ∀ v : ℂ, ‖fderiv ℝ G z v‖ ≤ K * (‖z‖ ^ (n + 1))⁻¹ * ‖v‖) :
    Tendsto (fderiv ℝ G) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ z : ℂ, R < ‖z‖ → ‖fderiv ℝ G z‖ ≤ K * (‖z‖ ^ (n + 1))⁻¹ := fun z hz =>
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (inv_nonneg.2 (by positivity)))
      (fun v => hG z hz v)
  have hlim : Tendsto (fun z : ℂ => K * (‖z‖ ^ (n + 1))⁻¹) (cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => (‖z‖ ^ (n + 1))⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp tendsto_norm_cocompact_atTop)
    simpa using h1.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  exact hbound z hz

theorem secOuterDecay_proof : SecOuterDecay := by
  intro m ψ b c' hm hψ hψb
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hm)
    have hnat : ((n : ℤ)).natAbs = n := by simp
    rw [hnat] at hψb
    have hR0 : 0 ≤ max b 0 := le_max_right b 0
    have hid : ∀ z : ℂ, max b 0 < ‖z‖ →
        Ang.ofProfile (n : ℤ) ψ z = c' * ((starRingEnd ℂ) z ^ n)⁻¹ := by
      intro z hz
      have hzpos : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt hR0 hz
      have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
      have hbz : b < ‖z‖ := lt_of_le_of_lt (le_max_left b 0) hz
      have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hzpos.ne'
      have h1 : z * (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      have hc : (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ) ^ 2 / z :=
        eq_div_of_mul_eq hz0 (by rw [mul_comm]; exact h1)
      simp only [Ang.ofProfile, Ang.angPhase, zpow_natCast]
      rw [hψb ‖z‖ hbz, hc]
      simp only [div_pow, inv_div]
      field_simp
      try ring
    have hEq : ∀ z : ℂ, max b 0 < ‖z‖ → Ang.ofProfile (n : ℤ) ψ =ᶠ[𝓝 z]
        (fun w : ℂ => c' * ((starRingEnd ℂ) w ^ n)⁻¹) := by
      intro z hz
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
      exact hid w hw
    have hG : ∀ z : ℂ, max b 0 < ‖z‖ → ∀ v : ℂ,
        ‖fderiv ℝ (fun w : ℂ => c' * ((starRingEnd ℂ) w ^ n)⁻¹) z v‖ ≤
          ‖c'‖ * n * (‖z‖ ^ (n + 1))⁻¹ * ‖v‖ := by
      intro z hz v
      have hz0 : z ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt hR0 hz)
      have hcf : (fun w : ℂ => c' * ((starRingEnd ℂ) w ^ n)⁻¹) =
          fun w : ℂ => (starRingEnd ℂ) ((starRingEnd ℂ) c' * (w ^ n)⁻¹) := by
        funext w
        simp
      rw [hcf]
      simpa [Complex.norm_conj] using decay_norm_conj (starRingEnd ℂ c') n hn hz0 v
    have hT := decay_tendsto (fun w : ℂ => c' * ((starRingEnd ℂ) w ^ n)⁻¹) n (‖c'‖ * n)
      (max b 0) (by positivity) hG
    have hev : (fderiv ℝ (fun w : ℂ => c' * ((starRingEnd ℂ) w ^ n)⁻¹)) =ᶠ[cocompact ℂ]
        (fderiv ℝ (Ang.ofProfile (n : ℤ) ψ)) := by
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max b 0)] with z hz
      exact (hEq z hz).fderiv_eq.symm
    exact hT.congr' hev
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hm)
    have hnat : (-(n : ℤ)).natAbs = n := by simp
    rw [hnat] at hψb
    have hR0 : 0 ≤ max b 0 := le_max_right b 0
    have hid : ∀ z : ℂ, max b 0 < ‖z‖ →
        Ang.ofProfile (-(n : ℤ)) ψ z = c' * (z ^ n)⁻¹ := by
      intro z hz
      have hzpos : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt hR0 hz
      have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
      have hbz : b < ‖z‖ := lt_of_le_of_lt (le_max_left b 0) hz
      have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hzpos.ne'
      simp only [Ang.ofProfile, Ang.angPhase, zpow_neg, zpow_natCast]
      rw [hψb ‖z‖ hbz]
      rw [div_pow]
      field_simp
    have hEq : ∀ z : ℂ, max b 0 < ‖z‖ → Ang.ofProfile (-(n : ℤ)) ψ =ᶠ[𝓝 z]
        (fun w : ℂ => c' * (w ^ n)⁻¹) := by
      intro z hz
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
      exact hid w hw
    have hG : ∀ z : ℂ, max b 0 < ‖z‖ → ∀ v : ℂ,
        ‖fderiv ℝ (fun w : ℂ => c' * (w ^ n)⁻¹) z v‖ ≤
          ‖c'‖ * n * (‖z‖ ^ (n + 1))⁻¹ * ‖v‖ := by
      intro z hz v
      have hz0 : z ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt hR0 hz)
      rw [decay_fderiv_holo _ _ z v (decay_hasDeriv c' n hz0)]
      exact decay_norm_holo c' n hn hz0 v
    have hT := decay_tendsto (fun w : ℂ => c' * (w ^ n)⁻¹) n (‖c'‖ * n)
      (max b 0) (by positivity) hG
    have hev : (fderiv ℝ (fun w : ℂ => c' * (w ^ n)⁻¹)) =ᶠ[cocompact ℂ]
        (fderiv ℝ (Ang.ofProfile (-(n : ℤ)) ψ)) := by
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max b 0)] with z hz
      exact (hEq z hz).fderiv_eq.symm
    exact hT.congr' hev

end UnforcedLeray.Short.PartI
