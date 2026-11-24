import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Slice
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.IntegrableWeight

/-!
# Part II-a, task `PartII-a:N02/4/7/3` (`nzmbWeightedEnergy`): the weighted energy identity

Source of record: `the November 2 reference manuscript`, lines 1722-1727.
Proof: (i) the four weighted integrands and the `A, B` integrands are integrable on
`Ioi 0 ×ˢ univ` (`nzmbIntegrableWeight`, applied to `G1, G2, ∂_η G1, ∂_η G2, A, B`; the band and
decay of `∂_η G_i` and of `A, B` come from `G_i` vanishing on the open set outside the band);
(ii) Fubini `setIntegral_prod` on both sides; (iii) on each slice the weight `s^{-3/2}` is constant
in `η`, so `nzmb_slice_energy` gives equality of the slice integrals.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem nzmbWeightedEnergy : NzmbWeightedEnergy := by
  intro k A B G1 G2 hG1 hG2 h hband hdec
  obtain ⟨s0, s1, hs0, hbnd⟩ := hband
  obtain ⟨κ, C, hκ, hb⟩ := hdec
  have hd1 : Differentiable ℝ G1 := hG1.differentiable (by simp)
  have hd2 : Differentiable ℝ G2 := hG2.differentiable (by simp)
  have hN : ∀ x : ℝ × ℝ, Complex.I * (k : ℂ) * G1 x - fderiv ℝ G2 x (0, 1) = A x ∧
      fderiv ℝ G1 x (0, 1) + Complex.I * (k : ℂ) * G2 x = B x := h
  -- Outside the band, `G1, G2` and their `η`-derivatives vanish.
  have hzero : ∀ x : ℝ × ℝ, x.1 ∉ Icc s0 s1 →
      G1 x = 0 ∧ G2 x = 0 ∧ fderiv ℝ G1 x (0, 1) = 0 ∧ fderiv ℝ G2 x (0, 1) = 0 := by
    intro x hx
    have hG0 : ∀ y : ℝ × ℝ, y.1 ∉ Icc s0 s1 → G1 y = 0 ∧ G2 y = 0 := by
      intro y hy
      by_contra hne
      have hor : G1 y ≠ 0 ∨ G2 y ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hne hc
      exact hy (hbnd y hor)
    have hU : IsOpen {y : ℝ × ℝ | y.1 ∉ Icc s0 s1} :=
      (isClosed_Icc.preimage continuous_fst).isOpen_compl
    have e1 : G1 =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hG0 y hy).1
    have e2 : G2 =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hG0 y hy).2
    refine ⟨(hG0 x hx).1, (hG0 x hx).2, ?_, ?_⟩
    · rw [e1.fderiv_eq]; simp
    · rw [e2.fderiv_eq]; simp
  have hG1b : ∀ y : ℝ × ℝ, G1 y ≠ 0 → y.1 ∈ Icc s0 s1 := fun y hy => hbnd y (Or.inl hy)
  have hG2b : ∀ y : ℝ × ℝ, G2 y ≠ 0 → y.1 ∈ Icc s0 s1 := fun y hy => hbnd y (Or.inr hy)
  have hD1b : ∀ y : ℝ × ℝ, fderiv ℝ G1 y (0, 1) ≠ 0 → y.1 ∈ Icc s0 s1 := by
    intro y hy
    by_contra hn
    exact hy (hzero y hn).2.2.1
  have hD2b : ∀ y : ℝ × ℝ, fderiv ℝ G2 y (0, 1) ≠ 0 → y.1 ∈ Icc s0 s1 := by
    intro y hy
    by_contra hn
    exact hy (hzero y hn).2.2.2
  -- Smoothness of the first derivatives.
  have hD1c : ContDiff ℝ ∞ (fun x : ℝ × ℝ => fderiv ℝ G1 x (0, 1)) :=
    (hG1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hD2c : ContDiff ℝ ∞ (fun x : ℝ × ℝ => fderiv ℝ G2 x (0, 1)) :=
    (hG2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  -- The data `A, B` are the one-mode combinations.
  have hAeq : A = fun x : ℝ × ℝ => Complex.I * (k : ℂ) * G1 x - fderiv ℝ G2 x (0, 1) :=
    funext fun x => ((hN x).1).symm
  have hBeq : B = fun x : ℝ × ℝ => fderiv ℝ G1 x (0, 1) + Complex.I * (k : ℂ) * G2 x :=
    funext fun x => ((hN x).2).symm
  have hAc : ContDiff ℝ ∞ A := by
    rw [hAeq]
    exact (contDiff_const.mul hG1).sub hD2c
  have hBc : ContDiff ℝ ∞ B := by
    rw [hBeq]
    exact hD1c.add (contDiff_const.mul hG2)
  have hAb : ∀ x : ℝ × ℝ, A x ≠ 0 → x.1 ∈ Icc s0 s1 := by
    intro x hx
    by_contra hn
    apply hx
    simp [hAeq, (hzero x hn).1, (hzero x hn).2.2.2]
  have hBb : ∀ x : ℝ × ℝ, B x ≠ 0 → x.1 ∈ Icc s0 s1 := by
    intro x hx
    by_contra hn
    apply hx
    simp [hBeq, (hzero x hn).2.2.1, (hzero x hn).2.1]
  -- Exponential decay of `A, B` with constant `(|k| + 1) C`.
  have hAdec : ∀ x : ℝ × ℝ, ‖A x‖ ≤ ((|k| + 1) * C) * Real.exp (-κ * |x.2|) := by
    intro x
    rw [hAeq]
    show ‖Complex.I * (k : ℂ) * G1 x - fderiv ℝ G2 x (0, 1)‖ ≤ _
    have h1 := hb x
    have hn : ‖Complex.I * (k : ℂ) * G1 x‖ = |k| * ‖G1 x‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have h2 : ‖Complex.I * (k : ℂ) * G1 x‖ ≤ |k| * (C * Real.exp (-κ * |x.2|)) := by
      rw [hn]; exact mul_le_mul_of_nonneg_left h1.1 (abs_nonneg k)
    calc ‖Complex.I * (k : ℂ) * G1 x - fderiv ℝ G2 x (0, 1)‖
        ≤ ‖Complex.I * (k : ℂ) * G1 x‖ + ‖fderiv ℝ G2 x (0, 1)‖ := norm_sub_le _ _
      _ ≤ |k| * (C * Real.exp (-κ * |x.2|)) + C * Real.exp (-κ * |x.2|) :=
          add_le_add h2 h1.2.2.2
      _ = ((|k| + 1) * C) * Real.exp (-κ * |x.2|) := by ring
  have hBdec : ∀ x : ℝ × ℝ, ‖B x‖ ≤ ((|k| + 1) * C) * Real.exp (-κ * |x.2|) := by
    intro x
    rw [hBeq]
    show ‖fderiv ℝ G1 x (0, 1) + Complex.I * (k : ℂ) * G2 x‖ ≤ _
    have h1 := hb x
    have hn : ‖Complex.I * (k : ℂ) * G2 x‖ = |k| * ‖G2 x‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have h2 : ‖Complex.I * (k : ℂ) * G2 x‖ ≤ |k| * (C * Real.exp (-κ * |x.2|)) := by
      rw [hn]; exact mul_le_mul_of_nonneg_left h1.2.2.1 (abs_nonneg k)
    calc ‖fderiv ℝ G1 x (0, 1) + Complex.I * (k : ℂ) * G2 x‖
        ≤ ‖fderiv ℝ G1 x (0, 1)‖ + ‖Complex.I * (k : ℂ) * G2 x‖ := norm_add_le _ _
      _ ≤ C * Real.exp (-κ * |x.2|) + |k| * (C * Real.exp (-κ * |x.2|)) :=
          add_le_add h1.2.1 h2
      _ = ((|k| + 1) * C) * Real.exp (-κ * |x.2|) := by ring
  -- Integrability of the weighted integrands on `Ioi 0 ×ˢ univ`.
  have IG1 := nzmbIntegrableWeight G1 hG1 s0 s1 κ C hs0 hκ hG1b (fun x => (hb x).1) 0
  have IG2 := nzmbIntegrableWeight G2 hG2 s0 s1 κ C hs0 hκ hG2b (fun x => (hb x).2.2.1) 0
  have ID1 := nzmbIntegrableWeight (fun x : ℝ × ℝ => fderiv ℝ G1 x (0, 1)) hD1c s0 s1 κ C hs0 hκ
    hD1b (fun x => (hb x).2.1) 0
  have ID2 := nzmbIntegrableWeight (fun x : ℝ × ℝ => fderiv ℝ G2 x (0, 1)) hD2c s0 s1 κ C hs0 hκ
    hD2b (fun x => (hb x).2.2.2) 0
  have IA := nzmbIntegrableWeight A hAc s0 s1 κ ((|k| + 1) * C) hs0 hκ hAb hAdec 0
  have IB := nzmbIntegrableWeight B hBc s0 s1 κ ((|k| + 1) * C) hs0 hκ hBb hBdec 0
  simp only [pow_zero, one_pow, one_mul] at IG1 IG2 ID1 ID2 IA IB
  have hFL : Integrable (fun x : ℝ × ℝ => (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2
      + k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
    have := (((IG1.const_mul (k ^ 2)).add ID1).add (IG2.const_mul (k ^ 2))).add ID2
    refine this.congr (ae_of_all _ fun x => ?_)
    try simp only [Pi.add_apply]
    ring
  have hFR : Integrable (fun x : ℝ × ℝ => (‖A x‖ ^ 2 + ‖B x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
    have := IA.add IB
    refine this.congr (ae_of_all _ fun x => ?_)
    try simp only [Pi.add_apply]
    ring
  have hLint : IntegrableOn (fun x : ℝ × ℝ => (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2
      + k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)))
      (Ioi 0 ×ˢ univ) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact hFL
  have hRint : IntegrableOn (fun x : ℝ × ℝ => (‖A x‖ ^ 2 + ‖B x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)))
      (Ioi 0 ×ˢ univ) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact hFR
  -- Fubini on both sides, then the slice identity.
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hLint, setIntegral_prod _ hRint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have hdecs : ∃ κ' C' : ℝ, 0 < κ' ∧ ∀ t : ℝ,
      ‖G1 (s, t)‖ ≤ C' * Real.exp (-κ' * |t|) ∧
      ‖deriv (fun τ : ℝ => G1 (s, τ)) t‖ ≤ C' * Real.exp (-κ' * |t|) ∧
      ‖G2 (s, t)‖ ≤ C' * Real.exp (-κ' * |t|) ∧
      ‖deriv (fun τ : ℝ => G2 (s, τ)) t‖ ≤ C' * Real.exp (-κ' * |t|) := by
    refine ⟨κ, C, hκ, fun t => ?_⟩
    rw [nzmb_deriv_slice G1 hd1 s t, nzmb_deriv_slice G2 hd2 s t]
    exact ⟨(hb (s, t)).1, (hb (s, t)).2.1, (hb (s, t)).2.2.1, (hb (s, t)).2.2.2⟩
  have hsl := nzmb_slice_energy k A B G1 G2 hG1 hG2 h s hdecs
  simp only [Measure.restrict_univ, integral_mul_const]
  rw [hsl]

end UnforcedLeray.Short.PartIIa
