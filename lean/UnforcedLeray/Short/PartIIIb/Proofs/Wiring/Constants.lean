import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Inputs

/-!
# The order of choice of the constants (task `PartIII-b:IIIb-D5/4`)

Source of record: `the November 2 reference manuscript` 5841-5857 (the choice of
`a = b_win`, `δ`, `m₀` after `K₀`, `k₀`, `d₀ = γ/3`).  We take `a = b = c` with
`c = 1/(1000(K+1)(k₀+1))`, `m₀ = min(cγ/96, d₋/11, γ/2000)`, and `δ` small so that
`η_δ = γ tanh(3δ/8) < min(cγ/48, γ/1000)`.
-/

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem constantsExist : UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ConstantsExist := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ConstantsExist
  intro γ dm K k0 hγ hdm
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1000 * ((K:ℝ) + 1) * ((k0:ℝ) + 1)) := ⟨_, rfl⟩
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
  have hk0 : (0:ℝ) ≤ k0 := Nat.cast_nonneg k0
  have hP : c * (1000 * ((K:ℝ) + 1) * ((k0:ℝ) + 1)) = 1 := by
    rw [hc]
    exact one_div_mul_cancel (by positivity)
  have hc0 : 0 < c := by
    rw [hc]
    apply div_pos one_pos
    positivity
  have hc1 : c ≤ 1 / 1000 := by
    nlinarith [mul_nonneg hc0.le hK0, mul_nonneg hc0.le hk0,
      mul_nonneg (mul_nonneg hc0.le hK0) hk0]
  have hKc : (K:ℝ) * c < 1 / 1000 := by
    nlinarith [mul_nonneg hc0.le hK0, mul_nonneg hc0.le hk0,
      mul_nonneg (mul_nonneg hc0.le hK0) hk0]
  have hk0c : (k0:ℝ) * c < 1 / 1000 := by
    nlinarith [mul_nonneg hc0.le hK0, mul_nonneg hc0.le hk0,
      mul_nonneg (mul_nonneg hc0.le hK0) hk0]
  have hθ : NearInst.thetaAB c c = c / 2 := by
    unfold NearInst.thetaAB
    have h1 : c / 2 ≤ min (1 / 100 : ℝ) (3 / 22) := le_min (by linarith) (by linarith)
    rw [min_self, min_eq_left h1]
  -- the background constant `m₀`
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℝ, m0 = min (c * γ / 96) (min (dm / 11) (γ / 2000)) := ⟨_, rfl⟩
  have hcg : 0 < c * γ := mul_pos hc0 hγ
  have hm0pos : 0 < m0 := by
    rw [hm0]
    exact lt_min (div_pos hcg (by norm_num))
      (lt_min (div_pos hdm (by norm_num)) (div_pos hγ (by norm_num)))
  have hm0a : m0 ≤ c * γ / 96 := by
    rw [hm0]; exact min_le_left _ _
  have hm0b : m0 ≤ dm / 11 := by
    rw [hm0]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm0c : m0 ≤ γ / 2000 := by
    rw [hm0]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- the bound on `δ`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (c / 48) (1 / 1000) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]; exact lt_min (by linarith) (by norm_num)
  have htA : t ≤ c / 48 := by
    rw [ht]; exact min_le_left _ _
  have htB : t ≤ 1 / 1000 := by
    rw [ht]; exact min_le_right _ _
  have hlog : 0 < Real.log (12 / 11) := Real.log_pos (by norm_num)
  have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), Real.tanh (3 * x / 8) < t ∧ x < Real.log (12 / 11) := by
    have hf : Continuous (fun x : ℝ => 3 * x / 8) := by fun_prop
    have hcont : Continuous (fun x : ℝ => Real.tanh (3 * x / 8)) := by
      simp only [Real.tanh_eq_sinh_div_cosh]
      exact Continuous.div (Real.continuous_sinh.comp hf) (Real.continuous_cosh.comp hf)
        (fun x => (Real.cosh_pos _).ne')
    have h0 := hcont.tendsto 0
    have h00 : Real.tanh (3 * (0:ℝ) / 8) = 0 := by simp
    rw [h00] at h0
    have h1 : ∀ᶠ x in 𝓝 (0:ℝ), Real.tanh (3 * x / 8) < t := h0.eventually (gt_mem_nhds ht0)
    have h2 : ∀ᶠ x in 𝓝 (0:ℝ), x < Real.log (12 / 11) := gt_mem_nhds hlog
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds h1).and
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds h2)
  obtain ⟨δ, ⟨hδtanh, hδlog⟩, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδpos' : 0 < δ := hδpos
  have htn : 0 ≤ Real.tanh (3 * δ / 8) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le
  have hetaN : 0 ≤ NearInst.etaDelta γ δ := by
    unfold NearInst.etaDelta
    exact mul_nonneg hγ.le htn
  have hηlt : γ * Real.tanh (3 * δ / 8) < γ * t := mul_lt_mul_of_pos_left hδtanh hγ
  have hηA : γ * t ≤ γ * (c / 48) := mul_le_mul_of_nonneg_left htA hγ.le
  have hηB : γ * t ≤ γ * (1 / 1000) := mul_le_mul_of_nonneg_left htB hγ.le
  have eA : γ * (c / 48) = c * γ / 48 := by ring
  have eB : γ * (1 / 1000) = γ / 1000 := by ring
  have he_lt1 : NearInst.etaDelta γ δ < c * γ / 48 := by
    unfold NearInst.etaDelta
    linarith
  have he_lt2 : NearInst.etaDelta γ δ < γ / 1000 := by
    unfold NearInst.etaDelta
    linarith
  have hc_lt1 : c < 1 := by linarith
  have hKab : (K:ℝ) * (c + c) < 1 / 100 := by
    have e : (K:ℝ) * (c + c) = 2 * ((K:ℝ) * c) := by ring
    rw [e]; linarith
  have hNear : ∀ C0 : ℝ, 0 < C0 → NearInst.NearChoice K γ dm c δ m0 C0 := by
    intro C0 hC0
    unfold NearInst.NearChoice
    refine ⟨c, NearInst.etaDelta γ δ + c * γ / 6 + 1, hc0, hc0, hc_lt1, hKab, hδpos', hm0pos,
      by linarith, ?_, ?_, ?_, hC0⟩
    · rw [hθ]
      have e : c / 2 * (γ / 3) / 8 = c * γ / 48 := by ring
      rw [e]; exact he_lt1
    · rw [hθ]
      have e : c / 2 * (γ / 3) / 8 = c * γ / 48 := by ring
      rw [e]; linarith
    · rw [hθ]
      have e : c / 2 * (γ / 3) = c * γ / 6 := by ring
      rw [e]; linarith
  refine ⟨c, δ, m0, hNear, hc0, hc_lt1, hδpos', hδlog, hm0pos, by linarith, by linarith, ?_,
    hetaN, he_lt2⟩
  have hkγ : (k0:ℝ) * c * γ < 1 / 1000 * γ := mul_lt_mul_of_pos_right hk0c hγ
  have e : (k0:ℝ) * c * (γ / 3) = (k0:ℝ) * c * γ / 3 := by ring
  rw [e]
  have hx1 : 0 ≤ (k0:ℝ) * c * γ := by
    have := mul_nonneg (mul_nonneg hk0 hc0.le) hγ.le
    exact this
  have e2 : 1 / 1000 * γ = γ / 1000 := by ring
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
