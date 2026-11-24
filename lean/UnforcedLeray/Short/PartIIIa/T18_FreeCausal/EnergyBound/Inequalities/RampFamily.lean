import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2

/-!
# Part III-a, task `PartIII-a:T18/3/2/1` (rampFamily): the `C¹` cutoff family

Source: `the November 2 reference manuscript` lines 3541-3552.
Cutoff `ψ(s) = σ((s-δ)/δ) · σ((2B-s)/B)` with `σ = Real.smoothTransition`: `C¹` (indeed `C^∞`),
`0 ≤ ψ ≤ 1`, compact support in `[δ, 2B] ⊂ (0,∞)`, `ψ = 1` on `[2δ, B]`, and `ψ' ≤ (C/δ)·1_{[δ,2δ]}`.
The constant is `C = 2K + 1` with `K` a bound for `|σ'|` (`σ' = 0` off `[0,1]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The ramp `ψ(s) = σ((s-δ)/δ) · σ((2B-s)/B)`, `σ = Real.smoothTransition`. -/
def rampPsi (δ B s : ℝ) : ℝ :=
  Real.smoothTransition ((s - δ) / δ) * Real.smoothTransition ((2 * B - s) / B)

theorem smooth_sigma_contDiff : ContDiff ℝ 1 Real.smoothTransition :=
  Real.smoothTransition.contDiff

theorem sigma_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  (smooth_sigma_contDiff.differentiable (by norm_num) x).hasDerivAt

/-- Chain rule for `σ ∘ h` at a point (`h` given explicitly so the composite unifies). -/
theorem sigma_comp_hasDerivAt {h : ℝ → ℝ} {h' x : ℝ} (hh : HasDerivAt h h' x) :
    HasDerivAt (fun y => Real.smoothTransition (h y)) (deriv Real.smoothTransition (h x) * h') x :=
  HasDerivAt.comp (h₂ := Real.smoothTransition) (h := h) x (sigma_hasDerivAt (h x)) hh

theorem sigma_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Monotone.deriv_nonneg Real.smoothTransition.monotone

theorem sigma_deriv_zero_of_lt_or_gt {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [h.deriv_eq]
    simp
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [h.deriv_eq]
    simp

theorem sigma_deriv_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv Real.smoothTransition x| ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    smooth_sigma_contDiff.continuous_deriv le_rfl
  obtain ⟨K0, hK0⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K0 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have h := hK0 x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have hx' : x < 0 ∨ 1 < x := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      exact hx
    rw [sigma_deriv_zero_of_lt_or_gt hx']
    simp

theorem rampPsi_eq_zero_of_lt {δ B s : ℝ} (hδ : 0 < δ) (hs : s < δ) : rampPsi δ B s = 0 := by
  have h1 : (s - δ) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ]
    linarith
  unfold rampPsi
  rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

theorem rampPsi_eq_zero_of_gt {δ B s : ℝ} (hB : 0 < B) (hs : 2 * B < s) :
    rampPsi δ B s = 0 := by
  have h1 : (2 * B - s) / B ≤ 0 := by
    rw [div_le_iff₀ hB]
    linarith
  unfold rampPsi
  rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]

theorem rampPsi_eq_zero_of_not_mem {δ B s : ℝ} (hδ : 0 < δ) (hB : 0 < B)
    (hs : s ∉ Icc δ (2 * B)) : rampPsi δ B s = 0 := by
  rcases lt_or_ge s δ with h | h
  · exact rampPsi_eq_zero_of_lt hδ h
  · have h2 : 2 * B < s := not_le.1 (fun hc => hs ⟨h, hc⟩)
    exact rampPsi_eq_zero_of_gt hB h2

theorem rampPsi_one {δ B s : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hs : s ∈ Icc (2 * δ) B) :
    rampPsi δ B s = 1 := by
  have h1 : 1 ≤ (s - δ) / δ := by
    rw [le_div_iff₀ hδ]
    linarith [hs.1]
  have h2 : 1 ≤ (2 * B - s) / B := by
    rw [le_div_iff₀ hB]
    linarith [hs.2]
  unfold rampPsi
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

theorem rampPsi_nonneg (δ B s : ℝ) : 0 ≤ rampPsi δ B s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem rampPsi_le_one (δ B s : ℝ) : rampPsi δ B s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/-- Derivative of the ramp at a point: the product rule with the two smooth factors. -/
theorem rampPsi_hasDerivAt (δ B s : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    deriv (rampPsi δ B) s =
      deriv Real.smoothTransition ((s - δ) / δ) * (1 / δ) * Real.smoothTransition ((2 * B - s) / B) +
        Real.smoothTransition ((s - δ) / δ) *
          (deriv Real.smoothTransition ((2 * B - s) / B) * ((0 - 1) / B)) := by
  have hin1 : HasDerivAt (fun y : ℝ => (y - δ) / δ) (1 / δ) s :=
    ((hasDerivAt_id' s).sub_const δ).div_const δ
  have hin2 : HasDerivAt (fun y : ℝ => (2 * B - y) / B) ((0 - 1) / B) s :=
    ((hasDerivAt_const s (2 * B)).sub (hasDerivAt_id' s)).div_const B
  have hf : HasDerivAt (fun y => Real.smoothTransition ((y - δ) / δ))
      (deriv Real.smoothTransition ((s - δ) / δ) * (1 / δ)) s :=
    sigma_comp_hasDerivAt hin1
  have hg : HasDerivAt (fun y => Real.smoothTransition ((2 * B - y) / B))
      (deriv Real.smoothTransition ((2 * B - s) / B) * ((0 - 1) / B)) s :=
    sigma_comp_hasDerivAt hin2
  unfold rampPsi
  exact (hf.mul hg).deriv

theorem rampFamily : UnforcedLeray.Short.IIIa.RampFamily := by
  obtain ⟨K, hK0, hK⟩ := sigma_deriv_bound
  refine ⟨2 * K + 1, by linarith, fun δ B hδ hB2 => ?_⟩
  have hB : 0 < B := by linarith
  refine ⟨rampPsi δ B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C¹` regularity
    unfold rampPsi
    exact (smooth_sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
      (smooth_sigma_contDiff.comp (((contDiff_const (c := 2 * B)).sub contDiff_id).div_const B))
  · -- compact support in `Icc δ (2B)`
    have hsupp : Function.support (rampPsi δ B) ⊆ Icc δ (2 * B) := by
      intro x hx
      by_contra hx'
      exact hx (rampPsi_eq_zero_of_not_mem hδ hB hx')
    have htsub : tsupport (rampPsi δ B) ⊆ Icc δ (2 * B) :=
      closure_minimal hsupp isClosed_Icc
    exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) htsub
  · -- support in `(0, ∞)`
    have hsupp : Function.support (rampPsi δ B) ⊆ Icc δ (2 * B) := by
      intro x hx
      by_contra hx'
      exact hx (rampPsi_eq_zero_of_not_mem hδ hB hx')
    have htsub : tsupport (rampPsi δ B) ⊆ Icc δ (2 * B) :=
      closure_minimal hsupp isClosed_Icc
    exact htsub.trans fun x hx => lt_of_lt_of_le hδ hx.1
  · -- values in `[0,1]`
    exact fun s => ⟨rampPsi_nonneg δ B s, rampPsi_le_one δ B s⟩
  · -- `ψ = 1` on `[2δ, B]`
    exact fun s hs => rampPsi_one hδ hB hs
  · -- derivative bound
    intro s
    by_cases hs : s ∈ Icc δ (2 * δ)
    · simp only [indicator_of_mem hs, mul_one]
      rw [rampPsi_hasDerivAt δ B s hδ hB]
      have ha := abs_le.1 (hK ((s - δ) / δ))
      have hb := abs_le.1 (hK ((2 * B - s) / B))
      have hf0 := rampPsi_nonneg δ B s
      have hf0' : Real.smoothTransition ((s - δ) / δ) ≤ 1 := Real.smoothTransition.le_one _
      have hg1 : 0 ≤ Real.smoothTransition ((2 * B - s) / B) := Real.smoothTransition.nonneg _
      have hg1' : Real.smoothTransition ((2 * B - s) / B) ≤ 1 := Real.smoothTransition.le_one _
      have hf0n : 0 ≤ Real.smoothTransition ((s - δ) / δ) := Real.smoothTransition.nonneg _
      have hp : 0 ≤ 1 / δ := by positivity
      have hq : 0 ≤ 1 / B := by positivity
      have hqp : 1 / B ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith [hs.1, hs.2])
      have ht : (0 - 1) / B = -(1 / B) := by ring
      rw [ht]
      have hgoal : (2 * K + 1) / δ = (2 * K + 1) * (1 / δ) := by ring
      rw [hgoal]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha.2) hp) hg1,
        mul_nonneg (mul_nonneg hK0 hp) (sub_nonneg.2 hg1'),
        mul_nonneg (mul_nonneg hf0n hq) (by linarith [hb.1] : (0 : ℝ) ≤ K + deriv Real.smoothTransition ((2 * B - s) / B)),
        mul_nonneg (mul_nonneg hK0 hq) (sub_nonneg.2 hf0'),
        mul_nonneg hK0 (sub_nonneg.2 hqp), hp]
    · rw [indicator_of_notMem hs, mul_zero]
      have hsc : s < δ ∨ 2 * δ < s := by
        by_contra hc
        exact hs ⟨not_lt.1 (fun h => hc (Or.inl h)), not_lt.1 (fun h => hc (Or.inr h))⟩
      rcases hsc with h | h
      · have hev : rampPsi δ B =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds h] with y hy
          exact rampPsi_eq_zero_of_lt hδ hy
        rw [hev.deriv_eq]
        simp
      · have hev : rampPsi δ B =ᶠ[𝓝 s] fun y => Real.smoothTransition ((2 * B - y) / B) := by
          filter_upwards [Ioi_mem_nhds h] with y hy
          have hy' : 2 * δ < y := hy
          have h1 : 1 ≤ (y - δ) / δ := by
            rw [le_div_iff₀ hδ]
            linarith
          unfold rampPsi
          rw [Real.smoothTransition.one_of_one_le h1, one_mul]
        rw [hev.deriv_eq]
        have hin2 : HasDerivAt (fun y : ℝ => (2 * B - y) / B) ((0 - 1) / B) s :=
          ((hasDerivAt_const s (2 * B)).sub (hasDerivAt_id' s)).div_const B
        have hd : HasDerivAt (fun y => Real.smoothTransition ((2 * B - y) / B))
            (deriv Real.smoothTransition ((2 * B - s) / B) * ((0 - 1) / B)) s :=
          sigma_comp_hasDerivAt hin2
        rw [hd.deriv]
        have h1 := sigma_deriv_nonneg ((2 * B - s) / B)
        have h2 : (0 - 1) / B ≤ 0 := by
          rw [div_le_iff₀ hB]
          linarith
        nlinarith

end UnforcedLeray.Short.IIIa
