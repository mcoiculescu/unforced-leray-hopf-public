import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.HpADiffS

/-!
Global-regularity version of `hpADiffS` (source 4973-4980): `Ay` is `C^2` on `(0,∞)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpADiffS_glob (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hC : ContDiffOn ℝ 2 (Ay ν χf A) (Ioi 0)) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun s' => hpA ν χf A s' x) s := by
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
  have hCnn : 0 ≤ 17 * ν * K1 + 6 * K2 := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 17) hν.le) hK1nn
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hK2nn
    linarith
  set Cm : ℝ := 17 * ν * K1 + 6 * K2 with hCm
  have hu : Summable (fun n : ℤ => Cm * (1 + |x.2|) ^ 5 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (sp_poly5_summable x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      (Cm * (1 + |x.2|) ^ 5)
  have hbound : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      ‖hpPhiD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x)‖ ≤
        Cm * (1 + |x.2|) ^ 5 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ hτ
    have hτJ : τ ∈ Icc (s / 2) (2 * s) := ⟨hτ.1.le, hτ.2.le⟩
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 := hpPhiD_bound ν τ hν hτ0 (xj ν n x) K1 K2 (Ay ν χf A τ) (deriv (Ay ν χf A) τ)
      (hMb τ hτJ) (hDb τ hτJ)
    refine h1.trans ?_
    have ha1τ : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν hτ0]
    exact sp5_major ν τ (1 + ν * (2 * s)) Cm Cm x n ha1τ (hPm τ hτJ) hCnn le_rfl hCnn
  have hdiff : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      HasDerivAt (fun τ' => hpPhi ν τ' (Ay ν χf A τ') (xj ν n x))
        (hpPhiD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x)) τ := by
    intro n τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact hpPhi_hasDerivAt ν (xj ν n x) (Ay ν χf A) (deriv (Ay ν χf A) τ) τ hν hτ0
      (hMd τ hτ0).hasDerivAt
  have hg0 : Summable (fun n : ℤ => hpPhi ν s (Ay ν χf A s) (xj ν n x)) := by
    have h := (hpPsiTermSummable ν χf A s x hν hs).1
    refine h.congr (fun n => ?_)
    exact hpATerm_eq_hpPhi ν χf A s x n (by linarith)
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun n τ => hpPhi ν τ (Ay ν χf A τ) (xj ν n x))
    (g' := fun n τ => hpPhiD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x))
    (u := fun n : ℤ => Cm * (1 + |x.2|) ^ 5 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => hdiff n τ hτ) (fun n τ hτ => hbound n τ hτ)
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  have hd : DifferentiableAt ℝ (fun τ => ∑' n : ℤ, hpPhi ν τ (Ay ν χf A τ) (xj ν n x)) s :=
    key.differentiableAt
  have hev : Filter.EventuallyEq (nhds s) (fun τ => hpA ν χf A τ x)
      (fun τ => ∑' n : ℤ, hpPhi ν τ (Ay ν χf A τ) (xj ν n x)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    rw [hpA_eq]
    exact tsum_congr fun j => hpATerm_eq_hpPhi ν χf A τ x j
      (by unfold ageA; nlinarith [mul_pos hν hτ0])
  exact hd.congr_of_eventuallyEq hev


end UnforcedLeray.Short.PartIIIb.Concrete
