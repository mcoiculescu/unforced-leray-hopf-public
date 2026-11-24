import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `PartIII-b:C/asrc/ra/5/4/10`: `GP54` implies the Gaussian-in-`q` term bound `TermBound`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
On a compact `K ⊆ Ioi 0` the time variable lies in `[sInf K, sSup K]`, and on a compact `L` the
variable `η` is bounded. The `GP54` bound then becomes a polynomial in `q` times
`exp(-q²/(κ a(s₁)))`, which is at most a constant times `exp(-d q²)` with `d = 1/(2κ a(s₁))`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A polynomial in `t ≥ 0` times `exp(-d t)` is uniformly bounded on `t ≥ 0`. -/
theorem gp54_polyexp_bound (N : ℕ) (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → (1 + c + t) ^ N * Real.exp (-d * t) ≤ K := by
  have hk : Tendsto (fun t : ℝ => (2 / d) ^ N * ((d * t) ^ N * Real.exp (-(d * t)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => d * t) atTop atTop := Tendsto.const_mul_atTop hd tendsto_id
    have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp h1).const_mul ((2 / d) ^ N)
    rw [mul_zero] at h2
    exact h2
  have hup : ∀ᶠ t in atTop, (1 + c + t) ^ N * Real.exp (-d * t)
      ≤ (2 / d) ^ N * ((d * t) ^ N * Real.exp (-(d * t))) := by
    filter_upwards [eventually_ge_atTop (1 + c)] with t ht
    have hpow : (1 + c + t) ^ N ≤ (2 * t) ^ N :=
      pow_le_pow_left₀ (by linarith) (by linarith) N
    have hsplit : (2 * t) ^ N = (2 / d) ^ N * (d * t) ^ N := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [neg_mul]
    calc (1 + c + t) ^ N * Real.exp (-(d * t)) ≤ (2 * t) ^ N * Real.exp (-(d * t)) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = (2 / d) ^ N * ((d * t) ^ N * Real.exp (-(d * t))) := by rw [hsplit]; ring
  have hlow : ∀ᶠ t in atTop, 0 ≤ (1 + c + t) ^ N * Real.exp (-d * t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  have hlim : Tendsto (fun t : ℝ => (1 + c + t) ^ N * Real.exp (-d * t)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk hlow hup
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hcont : ContinuousOn (fun t : ℝ => (1 + c + t) ^ N * Real.exp (-d * t)) (Icc 0 T) :=
    Continuous.continuousOn (by fun_prop)
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C0 1, (zero_le_one).trans (le_max_right _ _), fun t ht => ?_⟩
  by_cases htT : t ≤ T
  · have h1 := hC0 t ⟨ht, htT⟩
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_trans (le_abs_self _) h1) (le_max_left _ _)
  · rw [not_le] at htT
    exact le_trans (hT t htT.le).le (le_max_right _ _)

theorem gp54_termBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (n : ℕ) (f : ℝ × (ℝ × ℝ) → E) (hf : GP54 κ ν n f) : TermBound n f := by
  obtain ⟨_, hB⟩ := hf
  intro K hK hKc L hLc
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, 1, one_pos, fun m _ s hs => ?_⟩
    rw [hKe] at hs
    simp at hs
  · have hs0mem : sInf K ∈ K := hKc.sInf_mem hKne
    have hs1mem : sSup K ∈ K := hKc.sSup_mem hKne
    have hpos0 : 0 < sInf K := hK hs0mem
    have hs01 : sInf K ≤ sSup K := csInf_le hKc.bddBelow hs1mem
    have hKsub : ∀ s ∈ K, s ∈ Icc (sInf K) (sSup K) :=
      fun s hs => ⟨csInf_le hKc.bddBelow hs, le_csSup hKc.bddAbove hs⟩
    obtain ⟨C, N, hC0, hbd⟩ := hB (sInf K) (sSup K) hpos0 hs01
    have ha1 : 0 < ageA ν (sSup K) := by
      unfold ageA
      have : 0 < ν * sSup K := mul_pos hν (hK hs1mem)
      linarith
    have hκa : 0 < κ * ageA ν (sSup K) := mul_pos hκ ha1
    have hκa' : κ * ageA ν (sSup K) ≠ 0 := hκa.ne'
    obtain ⟨B, hB'⟩ := hLc.isBounded.exists_norm_le
    obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = 1 / (2 * (κ * ageA ν (sSup K))) := ⟨_, rfl⟩
    have hd : 0 < d := by
      rw [hd_def]
      exact div_pos one_pos (by linarith)
    obtain ⟨Kp, hKp0, hKp⟩ := gp54_polyexp_bound N (B ^ 2) d (sq_nonneg B) hd
    refine ⟨C * Kp, d, hd, fun m hm s hs q η hη => ?_⟩
    have hbnd := hbd m hm s (hKsub s hs) (q, η)
    have hη2 : η ^ 2 ≤ B ^ 2 := by
      have h1 := hB' η hη
      rw [Real.norm_eq_abs] at h1
      nlinarith [sq_abs η, abs_nonneg η]
    have hsq : sq2 (q, η) = q ^ 2 + η ^ 2 := rfl
    have hpow : (1 + sq2 (q, η)) ^ N ≤ (1 + B ^ 2 + q ^ 2) ^ N := by
      apply pow_le_pow_left₀
      · rw [hsq]; positivity
      · rw [hsq]; linarith
    have hexp1 : Real.exp (-(sq2 (q, η)) / (κ * ageA ν (sSup K)))
        ≤ Real.exp (-(q ^ 2) / (κ * ageA ν (sSup K))) := by
      apply Real.exp_le_exp.mpr
      rw [hsq]
      apply div_le_div_of_nonneg_right _ hκa.le
      linarith [sq_nonneg η]
    have hexpsplit : Real.exp (-(q ^ 2) / (κ * ageA ν (sSup K)))
        = Real.exp (-d * q ^ 2) * Real.exp (-d * q ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [hd_def]
      field_simp
      ring
    have hKq := hKp (q ^ 2) (sq_nonneg q)
    have hnonneg : 0 ≤ 1 + B ^ 2 + q ^ 2 := by nlinarith [sq_nonneg q, sq_nonneg B]
    calc ‖iteratedFDeriv ℝ m f (s, (q, η))‖
        ≤ C * (1 + sq2 (q, η)) ^ N * Real.exp (-(sq2 (q, η)) / (κ * ageA ν (sSup K))) := hbnd
      _ ≤ C * (1 + B ^ 2 + q ^ 2) ^ N * Real.exp (-(q ^ 2) / (κ * ageA ν (sSup K))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0) hexp1 (Real.exp_pos _).le
            (mul_nonneg hC0 (pow_nonneg hnonneg _))
      _ = C * ((1 + B ^ 2 + q ^ 2) ^ N * Real.exp (-d * q ^ 2)) * Real.exp (-d * q ^ 2) := by
          rw [hexpsplit]; ring
      _ ≤ C * Kp * Real.exp (-d * q ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKq hC0) (Real.exp_pos _).le

end UnforcedLeray.Short.PartIIIb.Concrete
