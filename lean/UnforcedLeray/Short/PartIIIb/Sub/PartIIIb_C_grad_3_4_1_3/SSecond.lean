import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.PsipASSecond

/-!
Global-regularity version of `psipASSecond` (source 4973-4980): `Ay` is `C^2` on `(0,∞)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipASSecond_glob (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hC : ContDiffOn ℝ 2 (Ay ν χf A) (Ioi 0)) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun s' => deriv (fun s'' => psipA ν χf A s'' x) s') s := by
  have hν0 : 0 ≤ ν := hν.le
  have hC1 : ContDiffOn ℝ 1 (Ay ν χf A) (Ioi 0) := hC.of_le (by norm_num)
  have hMd : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (Ay ν χf A) t := fun t ht =>
    (hC1.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds ht)
  have hC2D : ContDiffOn ℝ 1 (deriv (Ay ν χf A)) (Ioi 0) :=
    hC.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hDD : ContinuousOn (deriv (deriv (Ay ν χf A))) (Ioi 0) :=
    hC2D.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hDDif : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (deriv (Ay ν χf A)) t := fun t ht =>
    (hC2D.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds ht)
  have hJ : ∀ t ∈ Icc (s / 2) (2 * s), 0 < t := fun t ht => by linarith [ht.1]
  have hsJ : s ∈ Icc (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := Ay ν χf A) (fun t ht => (hMd t (hJ t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (Ay ν χf A)) (fun t ht => (hDDif t (hJ t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K3, hK3⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (deriv (Ay ν χf A))) (hDD.mono (fun t ht => hJ t ht))
  have hK1nn : 0 ≤ K1 := (norm_nonneg _).trans (hK1 s hsJ)
  have hK2nn : 0 ≤ K2 := (norm_nonneg _).trans (hK2 s hsJ)
  have hK3nn : 0 ≤ K3 := (norm_nonneg _).trans (hK3 s hsJ)
  have hMb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |Ay ν χf A t i j| ≤ K1 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK1 t ht)
  have hDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (Ay ν χf A) t i j| ≤ K2 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK2 t ht)
  have hDDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (deriv (Ay ν χf A)) t i j| ≤ K3 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK3 t ht)
  have hPm : ∀ t ∈ Icc (s / 2) (2 * s), ageA ν t ≤ 1 + ν * (2 * s) := by
    intro t ht
    unfold ageA
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hν0]
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hC0 : 0 ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) :=
    mul_nonneg (by positivity) (by linarith)
  have hsum : Summable (fun n : ℤ => 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (p2_polyk_summable 6 x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      (60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6)
  -- bounds on the three levels
  have hL0 : ∀ (n : ℤ) (τ : ℝ), τ ∈ Icc (s / 2) (2 * s) →
      |p2E ν (xj ν n x) τ * p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))|
        ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ ht
    have ht0 := hJ τ ht
    have ha1 : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht0]
    have hu0 : 0 ≤ p2U ν τ := by unfold p2U; exact inv_nonneg.mpr (by linarith)
    have hu1 : p2U ν τ ≤ 1 := by unfold p2U; exact inv_le_one_of_one_le₀ ha1
    have hTb : |p2TT (Ay ν χf A τ)| ≤ 2 * K1 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hMb τ ht 0 0, hMb τ ht 2 2])
    have hQb : |p2QQ (xj ν n x) (Ay ν χf A τ)| ≤ 8 * K1 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K1 _ hK1nn (norm_nonneg _) (hMb τ ht 0 0) (hMb τ ht 0 2)
        (hMb τ ht 2 0) (hMb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hA' := p2_A_bd (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) K1
      ‖xj ν n x‖ hu0 hu1 hK1nn hTb hQb
    have hL := p2_L0_bd (p2E ν (xj ν n x) τ) _ ν ‖xj ν n x‖ K1 K2 K3 (Real.exp_pos _).le hK1nn
      hK2nn hK3nn hν0 (norm_nonneg _) hA'
    exact hL.trans (p2_dom _ ν s τ hC0 ha1 (hPm τ ht) x n)
  have hL1 : ∀ (n : ℤ) (τ : ℝ), τ ∈ Icc (s / 2) (2 * s) →
      ‖p2Phi1 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)‖
        ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ ht
    rw [Real.norm_eq_abs]
    have ht0 := hJ τ ht
    have ha1 : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht0]
    have hu0 : 0 ≤ p2U ν τ := by unfold p2U; exact inv_nonneg.mpr (by linarith)
    have hu1 : p2U ν τ ≤ 1 := by unfold p2U; exact inv_le_one_of_one_le₀ ha1
    have hTb : |p2TT (Ay ν χf A τ)| ≤ 2 * K1 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hMb τ ht 0 0, hMb τ ht 2 2])
    have hQb : |p2QQ (xj ν n x) (Ay ν χf A τ)| ≤ 8 * K1 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K1 _ hK1nn (norm_nonneg _) (hMb τ ht 0 0) (hMb τ ht 0 2)
        (hMb τ ht 2 0) (hMb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hTDb : |p2TT (deriv (Ay ν χf A) τ)| ≤ 2 * K2 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hDb τ ht 0 0, hDb τ ht 2 2])
    have hQDb : |p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)| ≤ 8 * K2 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K2 _ hK2nn (norm_nonneg _) (hDb τ ht 0 0) (hDb τ ht 0 2)
        (hDb τ ht 2 0) (hDb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hA' := p2_A_bd (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) K1
      ‖xj ν n x‖ hu0 hu1 hK1nn hTb hQb
    have hB' := p2_B_bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
      (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)) K1 K2
      ‖xj ν n x‖ hν0 hu0 hu1 hK1nn hK2nn hTb hQb hTDb hQDb
    obtain ⟨hW0, hWle⟩ := p2_W_bd ν (xj ν n x) τ hν0 ha1
    have hL := p2_L1_bd (p2E ν (xj ν n x) τ) (p2W ν (xj ν n x) τ)
      (p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)))
      (p2B ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
        (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)))
      ν ‖xj ν n x‖ K1 K2 K3 (Real.exp_pos _).le hW0 hWle hν0 (norm_nonneg _) hK1nn hK2nn hK3nn
      hA' hB'
    exact hL.trans (p2_dom _ ν s τ hC0 ha1 (hPm τ ht) x n)
  have hL2 : ∀ (n : ℤ) (τ : ℝ), τ ∈ Icc (s / 2) (2 * s) →
      ‖p2Phi2 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (deriv (deriv (Ay ν χf A)) τ)‖
        ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ ht
    rw [Real.norm_eq_abs]
    have ht0 := hJ τ ht
    have ha1 : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht0]
    have hu0 : 0 ≤ p2U ν τ := by unfold p2U; exact inv_nonneg.mpr (by linarith)
    have hu1 : p2U ν τ ≤ 1 := by unfold p2U; exact inv_le_one_of_one_le₀ ha1
    have hTb : |p2TT (Ay ν χf A τ)| ≤ 2 * K1 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hMb τ ht 0 0, hMb τ ht 2 2])
    have hQb : |p2QQ (xj ν n x) (Ay ν χf A τ)| ≤ 8 * K1 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K1 _ hK1nn (norm_nonneg _) (hMb τ ht 0 0) (hMb τ ht 0 2)
        (hMb τ ht 2 0) (hMb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hTDb : |p2TT (deriv (Ay ν χf A) τ)| ≤ 2 * K2 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hDb τ ht 0 0, hDb τ ht 2 2])
    have hQDb : |p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)| ≤ 8 * K2 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K2 _ hK2nn (norm_nonneg _) (hDb τ ht 0 0) (hDb τ ht 0 2)
        (hDb τ ht 2 0) (hDb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hTDDb : |p2TT (deriv (deriv (Ay ν χf A)) τ)| ≤ 2 * K3 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hDDb τ ht 0 0, hDDb τ ht 2 2])
    have hQDDb : |p2QQ (xj ν n x) (deriv (deriv (Ay ν χf A)) τ)| ≤ 8 * K3 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K3 _ hK3nn (norm_nonneg _) (hDDb τ ht 0 0) (hDDb τ ht 0 2)
        (hDDb τ ht 2 0) (hDDb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hA' := p2_A_bd (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) K1
      ‖xj ν n x‖ hu0 hu1 hK1nn hTb hQb
    have hB' := p2_B_bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
      (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)) K1 K2
      ‖xj ν n x‖ hν0 hu0 hu1 hK1nn hK2nn hTb hQb hTDb hQDb
    have hBd' := p2_Bd_bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
      (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ))
      (p2TT (deriv (deriv (Ay ν χf A)) τ)) (p2QQ (xj ν n x) (deriv (deriv (Ay ν χf A)) τ))
      K1 K2 K3 ‖xj ν n x‖ hν0 hu0 hu1 hTb hQb hTDb hQDb hTDDb hQDDb
    obtain ⟨hW0, hWle⟩ := p2_W_bd ν (xj ν n x) τ hν0 ha1
    have hWd := p2_Wd_bd ν (xj ν n x) τ hν0 ha1
    have hL := p2_L2_bd (p2E ν (xj ν n x) τ) (p2W ν (xj ν n x) τ) (p2Wd ν (xj ν n x) τ)
      (p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)))
      (p2B ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
        (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)))
      (p2Bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
        (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ))
        (p2TT (deriv (deriv (Ay ν χf A)) τ)) (p2QQ (xj ν n x) (deriv (deriv (Ay ν χf A)) τ)))
      ν ‖xj ν n x‖ K1 K2 K3 (Real.exp_pos _).le hW0 hWle hWd hν0 (norm_nonneg _) hK1nn hK2nn
      hK3nn hA' hB' hBd'
    exact hL.trans (p2_dom _ ν s τ hC0 ha1 (hPm τ ht) x n)
  -- derivative pieces
  have hD1 : ∀ (n : ℤ) (τ : ℝ), 0 < τ →
      HasDerivAt (fun σ => p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ))
          (p2QQ (xj ν n x) (Ay ν χf A σ)))
        (p2Phi1 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)) τ :=
    fun n τ ht => p2_L1 ν τ (xj ν n x) hν ht ((hMd τ ht).hasDerivAt)
  have hD2 : ∀ (n : ℤ) (τ : ℝ), 0 < τ →
      HasDerivAt (fun σ => p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
        (p2Phi2 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)
          (deriv (deriv (Ay ν χf A)) τ)) τ :=
    fun n τ ht => p2_L2 ν τ (xj ν n x) hν ht ((hMd τ ht).hasDerivAt) ((hDDif τ ht).hasDerivAt)
  have hsP : ∀ τ : ℝ, 0 < τ → psipA ν χf A τ x = ∑' n : ℤ,
      p2E ν (xj ν n x) τ * p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) := by
    intro τ ht
    have ha : 0 < ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht]
    rw [psipA_eq_phi ν χf A τ x ha]
    exact tsum_congr fun n => p2_psiPhi_eq ν τ (Ay ν χf A τ) (xj ν n x)
  -- first derivative of the sum
  have hg0A : Summable (fun n : ℤ => p2E ν (xj ν n x) s * p2A (p2U ν s) (p2TT (Ay ν χf A s))
      (p2QQ (xj ν n x) (Ay ν χf A s))) :=
    Summable.of_norm_bounded hsum (fun n => by
      rw [Real.norm_eq_abs]; exact hL0 n s hsJ)
  have keyA : ∀ τ ∈ Ioo (s / 2) (2 * s), HasDerivAt
      (fun σ => ∑' n : ℤ, p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ))
        (p2QQ (xj ν n x) (Ay ν χf A σ)))
      (∑' n : ℤ, p2Phi1 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)) τ := fun τ hτ =>
    hasDerivAt_tsum_of_isPreconnected (u := fun n : ℤ => 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) *
        (1 + |x.2|) ^ 6 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
      (g := fun n σ => p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ))
        (p2QQ (xj ν n x) (Ay ν χf A σ)))
      (g' := fun n σ => p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
      (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := τ) hsum isOpen_Ioo isPreconnected_Ioo
      (fun n σ hσ => hD1 n σ (hJ σ (Ioo_subset_Icc_self hσ)))
      (fun n σ hσ => hL1 n σ (Ioo_subset_Icc_self hσ))
      ⟨by linarith, by linarith⟩ hg0A hτ
  have hev1 : (fun σ => psipA ν χf A σ x) =ᶠ[𝓝 s] (fun σ => ∑' n : ℤ,
      p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ)) (p2QQ (xj ν n x) (Ay ν χf A σ))) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with σ hσ
    exact hsP σ (by linarith [hσ.1])
  have hev2 : (fun σ => deriv (fun σ' => psipA ν χf A σ' x) σ) =ᶠ[𝓝 s]
      (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)) := by
    have e2 := hev1.deriv
    have e3 : (fun σ => deriv (fun σ' => ∑' n : ℤ,
        p2E ν (xj ν n x) σ' * p2A (p2U ν σ') (p2TT (Ay ν χf A σ'))
          (p2QQ (xj ν n x) (Ay ν χf A σ'))) σ) =ᶠ[𝓝 s]
        (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)) := by
      filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with σ hσ
      exact (keyA σ hσ).deriv
    exact e2.trans e3
  -- second derivative of the sum
  have hg0B : Summable (fun n : ℤ => p2Phi1 ν s (xj ν n x) (Ay ν χf A s) (deriv (Ay ν χf A) s)) :=
    Summable.of_norm_bounded hsum (fun n => by
      rw [Real.norm_eq_abs]; exact hL1 n s hsJ)
  have keyB : ∀ τ ∈ Ioo (s / 2) (2 * s), HasDerivAt
      (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
      (∑' n : ℤ, p2Phi2 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)
        (deriv (deriv (Ay ν χf A)) τ)) τ := fun τ hτ =>
    hasDerivAt_tsum_of_isPreconnected (u := fun n : ℤ => 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) *
        (1 + |x.2|) ^ 6 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
      (g := fun n σ => p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
      (g' := fun n σ => p2Phi2 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)
        (deriv (deriv (Ay ν χf A)) σ))
      (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := τ) hsum isOpen_Ioo isPreconnected_Ioo
      (fun n σ hσ => hD2 n σ (hJ σ (Ioo_subset_Icc_self hσ)))
      (fun n σ hσ => hL2 n σ (Ioo_subset_Icc_self hσ))
      ⟨by linarith, by linarith⟩ hg0B hτ
  have hdiffB : DifferentiableAt ℝ
      (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)) s :=
    (keyB s ⟨by linarith, by linarith⟩).differentiableAt
  exact hdiffB.congr_of_eventuallyEq hev2


end UnforcedLeray.Short.PartIIIb.Concrete
