import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.PsipAMixedS

/-!
Global-regularity version of `psipAMixedS` (source 4973-4980).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipAMixedS_glob (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hC : ContDiffOn ℝ 2 (Ay ν χf A) (Ioi 0)) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun s' => fderiv ℝ (psipA ν χf A s') x (ei 1)) s := by
  have hC1 : ContDiffOn ℝ 1 (Ay ν χf A) (Ioi 0) := hC.of_le (by norm_num)
  have hMd : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (Ay ν χf A) t := fun t ht =>
    (hC1.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds ht)
  have hDC : ContinuousOn (deriv (Ay ν χf A)) (Ioi 0) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hJpos : ∀ t ∈ Icc (s / 2) (2 * s), 0 < t := fun t ht => by linarith [ht.1]
  have hsJ : s ∈ Icc (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := Ay ν χf A) (fun t ht => (hMd t (hJpos t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (Ay ν χf A)) (hDC.mono (fun t ht => hJpos t ht))
  have hK1nn : 0 ≤ K1 := (norm_nonneg _).trans (hK1 s hsJ)
  have hK2nn : 0 ≤ K2 := (norm_nonneg _).trans (hK2 s hsJ)
  have hMb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |Ay ν χf A t i j| ≤ K1 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK1 t ht)
  have hDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (Ay ν χf A) t i j| ≤ K2 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK2 t ht)
  have hPm : ∀ t ∈ Icc (s / 2) (2 * s), ageA ν t ≤ 1 + ν * (2 * s) := by
    intro t ht
    unfold ageA
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hν.le]
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hC0 : 0 ≤ 20 * (1 + ν) * (K1 + K2) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hsum : Summable (fun n : ℤ => 20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (pam_poly5_summable x.1 _ (cOf ν) hα hc).mul_left (20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5)
  have hbdG : ∀ (n : ℤ) (t : ℝ), t ∈ Icc (s / 2) (2 * s) →
      |psiPhiD ν t (Ay ν χf A t) (xj ν n x) (0, 1)| ≤
        20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n t ht
    have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith [mul_pos hν (hJpos t ht)]
    refine (pam_G_bound ν t hν.le ha1 K1 K2 hK1nn hK2nn (Ay ν χf A t) (xj ν n x) (hMb t ht)).trans ?_
    exact pam_dom (20 * (1 + ν) * (K1 + K2)) ν s t hC0 ha1 (hPm t ht) x n
  have hbdGD : ∀ (n : ℤ) (t : ℝ), t ∈ Icc (s / 2) (2 * s) →
      ‖pamGD ν t (Ay ν χf A t) (deriv (Ay ν χf A) t) (xj ν n x)‖ ≤
        20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n t ht
    have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith [mul_pos hν (hJpos t ht)]
    rw [Real.norm_eq_abs]
    refine (pam_GD_bound ν t hν.le ha1 K1 K2 hK1nn hK2nn (Ay ν χf A t) (deriv (Ay ν χf A) t)
      (xj ν n x) (hMb t ht) (hDb t ht)).trans ?_
    exact pam_dom (20 * (1 + ν) * (K1 + K2)) ν s t hC0 ha1 (hPm t ht) x n
  have hg0 : Summable (fun n : ℤ => psiPhiD ν s (Ay ν χf A s) (xj ν n x) (0, 1)) :=
    Summable.of_norm_bounded hsum (fun n => by
      rw [Real.norm_eq_abs]; exact hbdG n s hsJ)
  have key := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℤ => 20 * (1 + ν) * (K1 + K2) *
      (1 + |x.2|) ^ 5 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (g := fun n τ => psiPhiD ν τ (Ay ν χf A τ) (xj ν n x) (0, 1))
    (g' := fun n τ => pamGD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s) hsum isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => pam_G_hasDerivAt ν τ hν (hJpos τ (Ioo_subset_Icc_self hτ)) (xj ν n x)
      ((hMd τ (hJpos τ (Ioo_subset_Icc_self hτ))).hasDerivAt))
    (fun n τ hτ => hbdGD n τ (Ioo_subset_Icc_self hτ))
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  have hfd : ∀ t : ℝ, 0 < t → fderiv ℝ (psipA ν χf A t) x (0, 1)
      = ∑' n : ℤ, psiPhiD ν t (Ay ν χf A t) (xj ν n x) (0, 1) := by
    intro t ht
    have ha : 0 < ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht]
    have hfun : psipA ν χf A t = fun z => ∑' j : ℤ, psiPhi ν t (Ay ν χf A t) (xj ν j z) :=
      funext fun z => psipA_eq_phi ν χf A t z ha
    rw [hfun]
    exact pam_fderiv ν t hν ht (Ay ν χf A t) x (0, 1)
  have hev : (fun s' => fderiv ℝ (psipA ν χf A s') x (0, 1)) =ᶠ[𝓝 s]
      (fun s' => ∑' n : ℤ, psiPhiD ν s' (Ay ν χf A s') (xj ν n x) (0, 1)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with τ hτ
    exact hfd τ (by linarith [hτ.1])
  have hd : DifferentiableAt ℝ
      (fun s' => ∑' n : ℤ, psiPhiD ν s' (Ay ν χf A s') (xj ν n x) (0, 1)) s := key.differentiableAt
  have hei : ei 1 = ((0:ℝ), (1:ℝ)) := rfl
  rw [hei]
  exact hd.congr_of_eventuallyEq hev


end UnforcedLeray.Short.PartIIIb.Concrete
