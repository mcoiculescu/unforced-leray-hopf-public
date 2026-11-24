import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.SPart

/-!
Global-regularity version of `psipASDiff` with the derivative formula (source 4973-4980).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipA_hasDerivAt_glob (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hC : ContDiffOn ℝ 2 (Ay ν χf A) (Ioi 0)) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => psipA ν χf A s' x)
      (∑' n : ℤ, sV ν (xj ν n x) (Ay ν χf A s) (deriv (Ay ν χf A) s) s) s := by
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
  have ha1s : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hC1nn : 0 ≤ 10 * ν * K1 + 8 * K2 + 8 * K1 := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hν.le) hK1nn
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK2nn
    have h3 := mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK1nn
    linarith
  have hu : Summable (fun n : ℤ => (10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (sp_poly4_summable x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      ((10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4)
  have hbound : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      ‖sV ν (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ‖ ≤
        (10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ hτ
    have hτJ : τ ∈ Icc (s / 2) (2 * s) := ⟨hτ.1.le, hτ.2.le⟩
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 := sV_bound ν hν (xj ν n x) K1 K2 (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ hτ0
      (hMb τ hτJ) (hDb τ hτJ)
    rw [Real.norm_eq_abs]
    refine h1.trans ?_
    have ha1τ : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν hτ0]
    exact sp_major ν τ (1 + ν * (2 * s)) (10 * ν * K1 + 8 * K2 + 8 * K1) (10 * ν * K1 + 8 * K2)
      x n ha1τ (hPm τ hτJ) (by nlinarith [mul_nonneg hν.le hK1nn, mul_nonneg hν.le hK2nn])
      (by linarith) hC1nn
  have hdiff : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      HasDerivAt (fun τ' => psiPhi ν τ' (Ay ν χf A τ') (xj ν n x))
        (sV ν (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ) τ := by
    intro n τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact sV_hasDerivAt ν hν (xj ν n x) (Ay ν χf A) (deriv (Ay ν χf A) τ) τ hτ0
      (hMd τ hτ0).hasDerivAt
  have hg0 : Summable (fun n : ℤ => psiPhi ν s (Ay ν χf A s) (xj ν n x)) := by
    refine Summable.of_norm_bounded hu (fun n => ?_)
    rw [Real.norm_eq_abs]
    have h1 := psiPhi_abs_le ν s ha1s (Ay ν χf A s) (xj ν n x)
    have hKm : 2 * Kmat (Ay ν χf A s) ≤ 8 * K1 := by
      unfold Kmat
      linarith [hMb s hsJ 0 0, hMb s hsJ 0 2, hMb s hsJ 2 0, hMb s hsJ 2 2]
    have hR1 : (1:ℝ) ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
    have hR3 : (1 + ‖xj ν n x‖) ^ 3 ≤ (1 + ‖xj ν n x‖) ^ 4 :=
      pow_le_pow_right₀ hR1 (by norm_num)
    have hE : 0 ≤ Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
    have hM := sp_major ν s (1 + ν * (2 * s)) (10 * ν * K1 + 8 * K2 + 8 * K1) (8 * K1) x n ha1s
      (hPm s hsJ) (by linarith)
      (by nlinarith [mul_nonneg hν.le hK1nn, mul_nonneg hν.le hK2nn]) hC1nn
    calc |psiPhi ν s (Ay ν χf A s) (xj ν n x)|
        ≤ 2 * Kmat (Ay ν χf A s) * ((1 + ‖xj ν n x‖) ^ 3 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := h1
      _ ≤ 8 * K1 * ((1 + ‖xj ν n x‖) ^ 3 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) :=
          mul_le_mul_of_nonneg_right hKm (mul_nonneg (pow_nonneg (by linarith [norm_nonneg (xj ν n x)]) 3) hE)
      _ ≤ 8 * K1 * ((1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR3 hE) (by linarith)
      _ = 8 * K1 * (1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := by ring
      _ ≤ _ := hM
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun n τ => psiPhi ν τ (Ay ν χf A τ) (xj ν n x))
    (g' := fun n τ => sV ν (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ)
    (u := fun n : ℤ => (10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => hdiff n τ hτ) (fun n τ hτ => hbound n τ hτ)
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  have hev : Filter.EventuallyEq (nhds s) (fun τ => psipA ν χf A τ x)
      (fun τ => ∑' n : ℤ, psiPhi ν τ (Ay ν χf A τ) (xj ν n x)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact psipA_eq_phi ν χf A τ x (by unfold ageA; nlinarith [mul_pos hν hτ0])
  exact key.congr_of_eventuallyEq hev


end UnforcedLeray.Short.PartIIIb.Concrete
