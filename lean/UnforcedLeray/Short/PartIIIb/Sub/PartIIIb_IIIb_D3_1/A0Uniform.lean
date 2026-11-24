import UnforcedLeray.Short.PartIIIb.Proofs.A0Unit

/-!
# `a0Unit` with constants uniform in `μ` on a compact window (source 4709-4730)

`T_a0Unit` is stated for one `μ`; its proof gives the explicit constant
`‖(21/4)ℓ‖ ∫ Φ_μ` with `Φ_μ = a0Phi M D μ (Re λ/2)`, `ν₀ = 1`, `b = Re λ/2`.  For `μ ∈ [lo, hi]`,
`0 < lo ≤ hi ≤ 1`, one has `Φ_μ ≤ Φ_lo + 2Φ_hi`, so the constant is uniform.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

theorem rpow_le_add_of_mem {t a b c : ℝ} (ht : 0 < t) (ha : a ≤ c) (hc : c ≤ b) :
    t ^ c ≤ t ^ a + t ^ b := by
  have h1 : 0 ≤ t ^ a := Real.rpow_nonneg ht.le _
  have h2 : 0 ≤ t ^ b := Real.rpow_nonneg ht.le _
  rcases le_total 1 t with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hc
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h ha
    linarith

theorem a0Phi_le_window {M D b lo hi μ : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hlo : 0 < lo)
    (hμlo : lo ≤ μ) (hμhi : μ ≤ hi) (hhi : hi ≤ 1) {t : ℝ} (ht : 0 < t) :
    a0Phi M D μ b t ≤ a0Phi M D lo b t + 2 * a0Phi M D hi b t := by
  unfold a0Phi
  have hE : 0 ≤ Real.exp (-(b * t)) := (Real.exp_pos _).le
  have p1 := rpow_le_add_of_mem ht (a := lo + 3 / 2) (b := hi + 3 / 2) (c := μ + 3 / 2)
    (by linarith) (by linarith)
  have p2 := rpow_le_add_of_mem ht (a := lo + 5 / 2) (b := hi + 5 / 2) (c := μ + 5 / 2)
    (by linarith) (by linarith)
  have q1 : 0 ≤ t ^ (lo + 3 / 2) := Real.rpow_nonneg ht.le _
  have q2 : 0 ≤ t ^ (hi + 3 / 2) := Real.rpow_nonneg ht.le _
  have q3 : 0 ≤ t ^ (lo + 5 / 2) := Real.rpow_nonneg ht.le _
  have q4 : 0 ≤ t ^ (hi + 5 / 2) := Real.rpow_nonneg ht.le _
  have c1 : D / (μ + 5 / 2) ≤ D / (lo + 5 / 2) :=
    div_le_div_of_nonneg_left hD (by linarith) (by linarith)
  have c2 : D / (μ + 5 / 2) ≤ 2 * (D / (hi + 5 / 2)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have c0 : 0 ≤ D / (μ + 5 / 2) := div_nonneg hD (by linarith)
  have c3 : 0 ≤ D / (lo + 5 / 2) := div_nonneg hD (by linarith)
  have c4 : 0 ≤ D / (hi + 5 / 2) := div_nonneg hD (by linarith)
  have h1 : 0 ≤ 1 + M := by linarith
  have A1 : (1 + M) * (t ^ (μ + 3 / 2) * Real.exp (-(b * t))) ≤
      (1 + M) * (t ^ (lo + 3 / 2) * Real.exp (-(b * t))) +
        2 * ((1 + M) * (t ^ (hi + 3 / 2) * Real.exp (-(b * t)))) := by
    have : t ^ (μ + 3 / 2) * Real.exp (-(b * t)) ≤
        t ^ (lo + 3 / 2) * Real.exp (-(b * t)) + t ^ (hi + 3 / 2) * Real.exp (-(b * t)) := by
      nlinarith
    nlinarith [mul_nonneg h1 (mul_nonneg q2 hE)]
  have A2 : D / (μ + 5 / 2) * (t ^ (μ + 5 / 2) * Real.exp (-(b * t))) ≤
      D / (lo + 5 / 2) * (t ^ (lo + 5 / 2) * Real.exp (-(b * t))) +
        2 * (D / (hi + 5 / 2) * (t ^ (hi + 5 / 2) * Real.exp (-(b * t)))) := by
    have e1 : D / (μ + 5 / 2) * (t ^ (μ + 5 / 2) * Real.exp (-(b * t))) ≤
        D / (μ + 5 / 2) * (t ^ (lo + 5 / 2) * Real.exp (-(b * t))) +
          D / (μ + 5 / 2) * (t ^ (hi + 5 / 2) * Real.exp (-(b * t))) := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ c0
      nlinarith
    have e2 : D / (μ + 5 / 2) * (t ^ (lo + 5 / 2) * Real.exp (-(b * t))) ≤
        D / (lo + 5 / 2) * (t ^ (lo + 5 / 2) * Real.exp (-(b * t))) :=
      mul_le_mul_of_nonneg_right c1 (mul_nonneg q3 hE)
    have e3 : D / (μ + 5 / 2) * (t ^ (hi + 5 / 2) * Real.exp (-(b * t))) ≤
        2 * (D / (hi + 5 / 2)) * (t ^ (hi + 5 / 2) * Real.exp (-(b * t))) :=
      mul_le_mul_of_nonneg_right c2 (mul_nonneg q4 hE)
    nlinarith [e1, e2, e3]
  linarith

theorem a0Unit_uniform {lam ell : ℂ} {chi dchi : ℝ → ℝ} (hlam : 0 < lam.re)
    (hd : ∀ x, HasDerivAt chi (dchi x) x) (hdc : Continuous dchi)
    (h1 : ∀ x, x ≤ 1 → chi x = 1) (h2 : ∀ x, 1.1 ≤ x → chi x = 0)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    ∃ C : ℝ, ∀ μ : ℝ, lo ≤ μ → μ ≤ hi → ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
      ‖aZero lam ell (μ : ℂ) (Bmu chi dchi ν μ) + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ)‖ ≤
        C * Real.exp (-(lam.re / 2) / ν) := by
  obtain ⟨M, D, hM0, hD0, hM, hD⟩ := a0_bounds hd hdc h1 h2
  have hb : 0 < lam.re / 2 := half_pos hlam
  have hcont : Continuous chi := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hIlo := a0Phi_integrable (M := M) (D := D) hlo hb
  have hIhi := a0Phi_integrable (M := M) (D := D) (hlo.trans_le hlohi) hb
  refine ⟨‖(21 / 4 : ℂ) * ell‖ * ((∫ t in Ioi (0 : ℝ), a0Phi M D lo (lam.re / 2) t) +
    2 * ∫ t in Ioi (0 : ℝ), a0Phi M D hi (lam.re / 2) t), ?_⟩
  intro μ hμlo hμhi ν hν hν1
  have hμ : 0 < μ := hlo.trans_le hμlo
  have hμC : -5 / 2 < (μ : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hFint : ∫ t in Ioi (0 : ℝ), a0F lam μ t =
      Complex.Gamma ((μ : ℂ) + 5 / 2) / lam ^ ((μ : ℂ) + 5 / 2) := by
    unfold a0F
    rw [UnforcedLeray.Special.integral_cpow_mul_cexp_laplace hμC hlam, Complex.cpow_neg]
    ring
  have hFi : IntegrableOn (a0F lam μ) (Ioi 0) := a0F_integrableOn hlam hM0 hD0 hμ
  have hGi : IntegrableOn (a0G lam chi dchi ν μ) (Ioi 0) :=
    a0G_integrableOn hlam hcont.measurable hdc.measurable hM hD hμ hν.le hν1
  have hA : aZero lam ell (μ : ℂ) (Bmu chi dchi ν μ) =
      -(21 / 4 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), a0G lam chi dchi ν μ t := by
    unfold aZero
    have hint : ∀ t : ℝ, (t : ℂ) ^ (μ : ℂ) * Complex.exp (-lam * (t : ℂ)) *
        (((Bd (Bmu chi dchi ν μ t) : ℝ) : ℂ) - Complex.I * ((Be (Bmu chi dchi ν μ t) : ℝ) : ℂ))
        = (21 / 2 : ℂ) * a0G lam chi dchi ν μ t := by
      intro t
      simp [Bd, Be, Bmu, Dzero, a0G, rMu, neg_mul]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hint t),
      MeasureTheory.integral_const_mul]
    ring
  have hkey : aZero lam ell (μ : ℂ) (Bmu chi dchi ν μ) + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ)
      = (21 / 4 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t) := by
    rw [hA, MeasureTheory.integral_sub hFi hGi, hFint, LCoeff]
    ring
  have hIμ := a0Phi_integrable (M := M) (D := D) (b := lam.re / 2) hμ hb
  have hI_le : ∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t ≤
      (∫ t in Ioi (0 : ℝ), a0Phi M D lo (lam.re / 2) t) +
        2 * ∫ t in Ioi (0 : ℝ), a0Phi M D hi (lam.re / 2) t := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add hIlo (hIhi.const_mul 2)]
    refine MeasureTheory.setIntegral_mono_on hIμ (hIlo.add (hIhi.const_mul 2))
      measurableSet_Ioi fun t ht => ?_
    exact a0Phi_le_window hM0 hD0 hlo hμlo hμhi hhi (Set.mem_Ioi.1 ht)
  have hint_bd : ‖∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t)‖ ≤
      Real.exp (-(lam.re / 2) / ν) * ∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.norm_integral_le_of_norm_le
      (Integrable.const_mul hIμ _) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      a0_diff_norm hlam hd h1 hM hD hM0 hD0 hμ hν hν1 (Set.mem_Ioi.1 ht)
  rw [hkey]
  calc ‖(21 / 4 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t)‖
      = ‖(21 / 4 : ℂ) * ell‖ * ‖∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t)‖ :=
        norm_mul _ _
    _ ≤ ‖(21 / 4 : ℂ) * ell‖ *
          (Real.exp (-(lam.re / 2) / ν) * ∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t) :=
        mul_le_mul_of_nonneg_left hint_bd (norm_nonneg _)
    _ ≤ ‖(21 / 4 : ℂ) * ell‖ *
          (Real.exp (-(lam.re / 2) / ν) * ((∫ t in Ioi (0 : ℝ), a0Phi M D lo (lam.re / 2) t) +
            2 * ∫ t in Ioi (0 : ℝ), a0Phi M D hi (lam.re / 2) t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI_le (Real.exp_pos _).le)
          (norm_nonneg _)
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb
