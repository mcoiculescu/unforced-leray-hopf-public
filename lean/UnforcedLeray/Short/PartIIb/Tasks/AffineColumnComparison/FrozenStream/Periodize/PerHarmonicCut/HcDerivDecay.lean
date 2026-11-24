import UnforcedLeray.Short.PartIIb.Sub.G4_2_3_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.CauchyPlanar

/-!
# Part II-b, item `PartII-b:G4/2/3/4/1`: `hcDerivDecay`

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

Outside the disc `ρ² < y₁² + y₂²` the function `Hc` agrees with `h(y) = M (y₁ - i y₂)^{-2}`.
Cauchy's estimate (`cauchy_planar`) on the disc of radius `|z|/2` about `z = y₁ - i y₂` gives
`‖∂ʲh(y)‖ · |y|² ≤ K_j`, which yields the `(1+|y₁|)^{-2}` decay since `|y| ≥ ρ`.
Inside the disc, the continuous function `y ↦ ‖∂ʲHc(y)‖` is bounded on a compact set.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Outside the disc, the `j`-th derivative of `h(y) = M (y₁ - i y₂)^{-2}` satisfies
`‖∂ʲh(y)‖ · (y₁² + y₂²) ≤ K` (Cauchy estimates, `cauchy_planar`). -/
lemma hcOut_bound (ρ : ℝ) (hρ : 0 < ρ) (M : ℂ) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ × ℝ, ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      ‖iteratedFDeriv ℝ j
          (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y‖
        * (y.1 ^ 2 + y.2 ^ 2) ≤ K := by
  obtain ⟨A, hA⟩ := cauchy_planar j
  refine ⟨|A| * ‖M‖ * 4 * 2 ^ j / ρ ^ j, div_nonneg (by positivity) (pow_nonneg hρ.le j), ?_⟩
  intro y hy
  set z : ℂ := (y.1 : ℂ) - (y.2 : ℂ) * Complex.I with hzdef
  have hR2 : ‖z‖ ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzdef]
    simp <;> ring
  have hRρ : ρ < ‖z‖ := by nlinarith [norm_nonneg z]
  have hRpos : 0 < ‖z‖ := lt_trans hρ hRρ
  have hz0 : ‖z‖ ≠ 0 := hRpos.ne'
  have hzz : (z.re, -z.im) = y := by
    apply Prod.ext
    · simp [hzdef]
    · simp [hzdef]
  -- points of the disc of radius `‖z‖/2` about `z` stay away from the origin
  have hball : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), ‖z‖ / 2 ≤ ‖w‖ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le z w
    have h2 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
    linarith
  have hne : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), w ≠ 0 := by
    intro w hw h0
    have h1 := hball w hw
    rw [h0, norm_zero] at h1
    linarith
  have hd : DifferentiableOn ℂ (fun w : ℂ => M * w ^ (-2 : ℤ)) (Metric.closedBall z (‖z‖ / 2)) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    exact (differentiableAt_id.zpow (Or.inl (hne w hw))).const_mul M
  have hbd : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), ‖M * w ^ (-2 : ℤ)‖ ≤ ‖M‖ * 4 / ‖z‖ ^ 2 := by
    intro w hw
    have h1 := hball w hw
    have hpos : 0 < ‖z‖ / 2 := half_pos hRpos
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hpos h1
    rw [norm_mul, norm_zpow, zpow_neg, zpow_two]
    have h6 : (‖w‖ * ‖w‖)⁻¹ ≤ (‖z‖ / 2 * (‖z‖ / 2))⁻¹ :=
      inv_anti₀ (mul_pos hpos hpos) (mul_self_le_mul_self hpos.le h1)
    have h5 : (‖z‖ / 2 * (‖z‖ / 2))⁻¹ = 4 / ‖z‖ ^ 2 := by
      field_simp <;> ring
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (h6.trans_eq h5) (norm_nonneg _)
  have hCau : ‖iteratedFDeriv ℝ j
      (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) (z.re, -z.im)‖
      ≤ A * (‖M‖ * 4 / ‖z‖ ^ 2) / (‖z‖ / 2) ^ j :=
    hA (fun w : ℂ => M * w ^ (-2 : ℤ)) (‖z‖ / 2) (‖M‖ * 4 / ‖z‖ ^ 2) z (half_pos hRpos) hd hbd
  rw [hzz] at hCau
  rw [← hR2]
  have hAabs : A ≤ |A| := le_abs_self A
  calc ‖iteratedFDeriv ℝ j
          (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y‖
        * ‖z‖ ^ 2
      ≤ A * (‖M‖ * 4 / ‖z‖ ^ 2) / (‖z‖ / 2) ^ j * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCau (by positivity)
    _ = A * ‖M‖ * 4 * 2 ^ j / ‖z‖ ^ j := by
        rw [div_pow]
        field_simp <;> ring
    _ ≤ |A| * ‖M‖ * 4 * 2 ^ j / ‖z‖ ^ j := by
        have hM : 0 ≤ ‖M‖ * 4 * 2 ^ j := by positivity
        exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hAabs hM])
          (by positivity)
    _ ≤ |A| * ‖M‖ * 4 * 2 ^ j / ρ ^ j :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hρ j) (pow_le_pow_left₀ hρ.le hRρ.le j)

/-- **`hcDerivDecay`** (SP 2349-2358): every derivative of the cut harmonic part decays like
`(1+|y₁|)^{-2}`. -/
theorem hcDerivDecay : UnforcedLeray.Short.IIb.HcDerivDecay := by
  unfold HcDerivDecay
  intro Hc ρ M hHc hρ hout j
  obtain ⟨K, hK0, hK⟩ := hcOut_bound ρ hρ M j
  have hjle : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcont : Continuous (fun y : ℝ × ℝ => iteratedFDeriv ℝ j Hc y) :=
    hHc.continuous_iteratedFDeriv hjle
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : ℝ × ℝ) ρ).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C0 0 * (1 + ρ) ^ 2 + (1 + 1 / ρ) ^ 2 * K, fun y => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  by_cases hy : ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2
  · -- outside the disc: `Hc` coincides with `h` on an open neighbourhood of `y`
    have hopen : IsOpen {x : ℝ × ℝ | ρ ^ 2 < x.1 ^ 2 + x.2 ^ 2} :=
      isOpen_lt continuous_const (by fun_prop)
    have hEv : Hc =ᶠ[𝓝 y]
        (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) (fun x hx => hout x hx)
    have hpt := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEv j
    rw [hpt.eq_of_nhds]
    obtain ⟨s, hs0, hss, hsρ⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = y.1 ^ 2 + y.2 ^ 2 ∧ ρ < s :=
      ⟨Real.sqrt (y.1 ^ 2 + y.2 ^ 2), Real.sqrt_nonneg _,
        Real.sq_sqrt (by positivity),
        by
          have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ y.1 ^ 2 + y.2 ^ 2 by positivity)
          have h2 := Real.sqrt_nonneg (y.1 ^ 2 + y.2 ^ 2)
          nlinarith⟩
    have h1 : |y.1| ≤ s := by nlinarith [sq_abs y.1, abs_nonneg y.1, sq_nonneg y.2, hs0, hss]
    have h2 : 1 + |y.1| ≤ (1 + 1 / ρ) * s := by
      have h3 : 1 ≤ s / ρ := by
        rw [le_div_iff₀ hρ]
        linarith
      have e : (1 + 1 / ρ) * s = s + s / ρ := by ring
      linarith
    have hsq : (1 + |y.1|) ^ 2 ≤ (1 + 1 / ρ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by
      rw [← hss]
      calc (1 + |y.1|) ^ 2 ≤ ((1 + 1 / ρ) * s) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h2 2
        _ = (1 + 1 / ρ) ^ 2 * s ^ 2 := by ring
    calc ‖iteratedFDeriv ℝ j
            (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y‖
          * (1 + |y.1|) ^ 2
        ≤ ‖iteratedFDeriv ℝ j
            (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y‖
          * ((1 + 1 / ρ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
      _ = (1 + 1 / ρ) ^ 2 * (‖iteratedFDeriv ℝ j
            (fun x : ℝ × ℝ => M * (((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) y‖
          * (y.1 ^ 2 + y.2 ^ 2)) := by ring
      _ ≤ (1 + 1 / ρ) ^ 2 * K :=
          mul_le_mul_of_nonneg_left (hK y hy) (by positivity)
      _ ≤ max C0 0 * (1 + ρ) ^ 2 + (1 + 1 / ρ) ^ 2 * K :=
          le_add_of_nonneg_left (mul_nonneg (le_max_right C0 0) (by positivity))
  · -- inside the disc: compactness
    push_neg at hy
    have habs : |y.1| ≤ ρ := by nlinarith [sq_nonneg y.2, sq_abs y.1, abs_nonneg y.1, hρ]
    have habs2 : |y.2| ≤ ρ := by nlinarith [sq_nonneg y.1, sq_abs y.2, abs_nonneg y.2, hρ]
    have hmem : y ∈ Metric.closedBall (0 : ℝ × ℝ) ρ := by
      rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
      exact ⟨habs, habs2⟩
    have h0 : ‖iteratedFDeriv ℝ j Hc y‖ ≤ C0 := hC0 y hmem
    have hsq2 : (1 + |y.1|) ^ 2 ≤ (1 + ρ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc ‖iteratedFDeriv ℝ j Hc y‖ * (1 + |y.1|) ^ 2
        ≤ max C0 0 * (1 + |y.1|) ^ 2 :=
          mul_le_mul_of_nonneg_right (h0.trans (le_max_left C0 0)) (by positivity)
      _ ≤ max C0 0 * (1 + ρ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq2 (le_max_right C0 0)
      _ ≤ max C0 0 * (1 + ρ) ^ 2 + (1 + 1 / ρ) ^ 2 * K :=
          le_add_of_nonneg_right (mul_nonneg (by positivity) hK0)

end UnforcedLeray.Short.IIb
