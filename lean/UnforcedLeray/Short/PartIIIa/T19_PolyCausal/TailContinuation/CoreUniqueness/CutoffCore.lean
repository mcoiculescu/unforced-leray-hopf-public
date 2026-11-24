import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities

/-!
# Part III-a, helper 5 of `PartIII-a:T19/3/4`: smooth exponential ramp cutoff localized to `[δ, B₂]`

Defines `coreRampPsi δ B B₂ s = σ((s - δ)/δ) · σ((B₂ - s)/(B₂ - B))` and
`coreExpRamp L δ B B₂ s = exp(-L s) · coreRampPsi δ B B₂ s` for `0 < δ`, `2 δ < B < B₂`.
Unlike `rampPsi δ B` (which ramps down on `[B, 2B]`), `coreRampPsi δ B B₂` ramps down on
`[B, B₂]`, allowing `B` to be arbitrarily close to `H` while keeping the support inside
`[δ, B₂] ⊂ (0, H')`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Smooth ramp cutoff equal to `1` on `[2δ, B]` and supported in `[δ, B₂]`. -/
def coreRampPsi (δ B B₂ s : ℝ) : ℝ :=
  Real.smoothTransition ((s - δ) / δ) * Real.smoothTransition ((B₂ - s) / (B₂ - B))

theorem coreRampPsi_contDiff (δ B B₂ : ℝ) : ContDiff ℝ ∞ (coreRampPsi δ B B₂) := by
  unfold coreRampPsi
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (Real.smoothTransition.contDiff.comp
      (((contDiff_const (c := B₂)).sub contDiff_id).div_const (B₂ - B)))

theorem coreRampPsi_eq_zero_of_lt {δ B B₂ s : ℝ} (hδ : 0 < δ) (hs : s < δ) :
    coreRampPsi δ B B₂ s = 0 := by
  have h1 : (s - δ) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ]
    linarith
  unfold coreRampPsi
  rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

theorem coreRampPsi_eq_zero_of_gt {δ B B₂ s : ℝ} (hBB₂ : B < B₂) (hs : B₂ < s) :
    coreRampPsi δ B B₂ s = 0 := by
  have h1 : (B₂ - s) / (B₂ - B) ≤ 0 := by
    rw [div_le_iff₀ (sub_pos.2 hBB₂)]
    linarith
  unfold coreRampPsi
  rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]

theorem coreRampPsi_eq_zero_of_not_mem {δ B B₂ s : ℝ} (hδ : 0 < δ) (hBB₂ : B < B₂)
    (hs : s ∉ Icc δ B₂) : coreRampPsi δ B B₂ s = 0 := by
  rcases lt_or_ge s δ with h | h
  · exact coreRampPsi_eq_zero_of_lt hδ h
  · have h2 : B₂ < s := not_le.1 (fun hc => hs ⟨h, hc⟩)
    exact coreRampPsi_eq_zero_of_gt hBB₂ h2

theorem coreRampPsi_one {δ B B₂ s : ℝ} (hδ : 0 < δ) (hBB₂ : B < B₂) (hs : s ∈ Icc (2 * δ) B) :
    coreRampPsi δ B B₂ s = 1 := by
  have h1 : 1 ≤ (s - δ) / δ := by
    rw [le_div_iff₀ hδ]
    linarith [hs.1]
  have h2 : 1 ≤ (B₂ - s) / (B₂ - B) := by
    rw [le_div_iff₀ (sub_pos.2 hBB₂)]
    linarith [hs.2]
  unfold coreRampPsi
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

theorem coreRampPsi_nonneg (δ B B₂ s : ℝ) : 0 ≤ coreRampPsi δ B B₂ s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem coreRampPsi_deriv_le {K δ B B₂ : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hδ : 0 < δ) (hB2 : 2 * δ < B)
    (hBB₂ : B < B₂) (s : ℝ) :
    deriv (coreRampPsi δ B B₂) s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  have hBB₂_pos : 0 < B₂ - B := sub_pos.2 hBB₂
  by_cases hs : s ∈ Icc δ (2 * δ)
  · simp only [indicator_of_mem hs, mul_one]
    have hsB : s < B := lt_of_le_of_lt hs.2 hB2
    have hev : coreRampPsi δ B B₂ =ᶠ[𝓝 s] fun y => Real.smoothTransition ((y - δ) / δ) := by
      filter_upwards [Iio_mem_nhds hsB] with y hy
      have hy' : y < B := hy
      have h2 : 1 ≤ (B₂ - y) / (B₂ - B) := by
        rw [le_div_iff₀ hBB₂_pos]
        linarith
      unfold coreRampPsi
      rw [Real.smoothTransition.one_of_one_le h2, mul_one]
    rw [hev.deriv_eq]
    have hin1 : HasDerivAt (fun y : ℝ => (y - δ) / δ) (1 / δ) s :=
      ((hasDerivAt_id' s).sub_const δ).div_const δ
    have hd : HasDerivAt (fun y => Real.smoothTransition ((y - δ) / δ))
        (deriv Real.smoothTransition ((s - δ) / δ) * (1 / δ)) s :=
      sigma_comp_hasDerivAt hin1
    rw [hd.deriv]
    have ha := (abs_le.1 (hK ((s - δ) / δ))).2
    have hp : 0 ≤ 1 / δ := by positivity
    calc deriv Real.smoothTransition ((s - δ) / δ) * (1 / δ)
        ≤ K * (1 / δ) := mul_le_mul_of_nonneg_right ha hp
      _ ≤ (2 * K + 1) * (1 / δ) := mul_le_mul_of_nonneg_right (by linarith) hp
      _ = (2 * K + 1) / δ := by ring
  · rw [indicator_of_notMem hs, mul_zero]
    have hsc : s < δ ∨ 2 * δ < s := by
      by_contra hc
      exact hs ⟨not_lt.1 (fun h => hc (Or.inl h)), not_lt.1 (fun h => hc (Or.inr h))⟩
    rcases hsc with h | h
    · have hev : coreRampPsi δ B B₂ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact coreRampPsi_eq_zero_of_lt hδ hy
      rw [hev.deriv_eq]
      simp
    · have hev : coreRampPsi δ B B₂ =ᶠ[𝓝 s]
          fun y => Real.smoothTransition ((B₂ - y) / (B₂ - B)) := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 * δ < y := hy
        have h1 : 1 ≤ (y - δ) / δ := by
          rw [le_div_iff₀ hδ]
          linarith
        unfold coreRampPsi
        rw [Real.smoothTransition.one_of_one_le h1, one_mul]
      rw [hev.deriv_eq]
      have hin2 : HasDerivAt (fun y : ℝ => (B₂ - y) / (B₂ - B)) ((0 - 1) / (B₂ - B)) s :=
        ((hasDerivAt_const s B₂).sub (hasDerivAt_id' s)).div_const (B₂ - B)
      have hd : HasDerivAt (fun y => Real.smoothTransition ((B₂ - y) / (B₂ - B)))
          (deriv Real.smoothTransition ((B₂ - s) / (B₂ - B)) * ((0 - 1) / (B₂ - B))) s :=
        sigma_comp_hasDerivAt hin2
      rw [hd.deriv]
      have h1 := sigma_deriv_nonneg ((B₂ - s) / (B₂ - B))
      have h2 : (0 - 1) / (B₂ - B) ≤ 0 := by
        rw [div_le_iff₀ hBB₂_pos]
        linarith
      nlinarith

/-- Exponentially weighted smooth ramp cutoff supported in `[δ, B₂]`. -/
def coreExpRamp (L δ B B₂ s : ℝ) : ℝ :=
  Real.exp (-L * s) * coreRampPsi δ B B₂ s

theorem coreExpRamp_contDiff (L δ B B₂ : ℝ) : ContDiff ℝ ∞ (coreExpRamp L δ B B₂) := by
  unfold coreExpRamp
  exact (((contDiff_const (c := -L)).mul contDiff_id).exp).mul (coreRampPsi_contDiff δ B B₂)

theorem coreExpRamp_eq_zero_of_not_mem {L δ B B₂ s : ℝ} (hδ : 0 < δ) (hBB₂ : B < B₂)
    (hs : s ∉ Icc δ B₂) : coreExpRamp L δ B B₂ s = 0 := by
  unfold coreExpRamp
  rw [coreRampPsi_eq_zero_of_not_mem hδ hBB₂ hs, mul_zero]

theorem coreExpRamp_tsupport_subset {L δ B B₂ : ℝ} (hδ : 0 < δ) (hBB₂ : B < B₂) :
    tsupport (coreExpRamp L δ B B₂) ⊆ Icc δ B₂ := by
  have hsupp : Function.support (coreExpRamp L δ B B₂) ⊆ Icc δ B₂ := by
    intro s hs
    by_contra hs'
    exact hs (coreExpRamp_eq_zero_of_not_mem hδ hBB₂ hs')
  exact closure_minimal hsupp isClosed_Icc

theorem coreExpRamp_nonneg (L δ B B₂ s : ℝ) : 0 ≤ coreExpRamp L δ B B₂ s :=
  mul_nonneg (Real.exp_nonneg _) (coreRampPsi_nonneg δ B B₂ s)

theorem coreExpRamp_ge_on_Icc {L δ B B₂ s : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hBB₂ : B < B₂)
    (hs : s ∈ Icc (2 * δ) B) :
    Real.exp (-L * B) ≤ coreExpRamp L δ B B₂ s := by
  unfold coreExpRamp
  rw [coreRampPsi_one hδ hBB₂ hs, mul_one]
  exact Real.exp_le_exp.2 (by nlinarith [hs.2])

theorem coreExpRamp_deriv_add (L δ B B₂ s : ℝ) :
    deriv (coreExpRamp L δ B B₂) s + L * coreExpRamp L δ B B₂ s =
      Real.exp (-L * s) * deriv (coreRampPsi δ B B₂) s := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-L * y)) (Real.exp (-L * s) * (-L * 1)) s :=
    HasDerivAt.exp ((hasDerivAt_id' s).const_mul (-L))
  have h2 : HasDerivAt (coreRampPsi δ B B₂) (deriv (coreRampPsi δ B B₂) s) s :=
    ((coreRampPsi_contDiff δ B B₂).differentiable (by simp) s).hasDerivAt
  have hd : deriv (coreExpRamp L δ B B₂) s =
      Real.exp (-L * s) * (-L * 1) * coreRampPsi δ B B₂ s +
        Real.exp (-L * s) * deriv (coreRampPsi δ B B₂) s := by
    unfold coreExpRamp
    exact (h1.mul h2).deriv
  rw [hd]
  unfold coreExpRamp
  ring

theorem coreExpRamp_deriv_add_le {K L δ B B₂ : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hB2 : 2 * δ < B) (hBB₂ : B < B₂) (s : ℝ) :
    deriv (coreExpRamp L δ B B₂) s + L * coreExpRamp L δ B B₂ s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  rw [coreExpRamp_deriv_add]
  have hd := coreRampPsi_deriv_le hK0 hK hδ hB2 hBB₂ s
  have hexp0 : 0 ≤ Real.exp (-L * s) := Real.exp_nonneg _
  calc Real.exp (-L * s) * deriv (coreRampPsi δ B B₂) s
      ≤ Real.exp (-L * s) *
          ((2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s) :=
        mul_le_mul_of_nonneg_left hd hexp0
    _ ≤ (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
        by_cases hs : s ∈ Icc δ (2 * δ)
        · rw [indicator_of_mem hs, mul_one]
          have hs0 : 0 ≤ s := le_trans hδ.le hs.1
          have hexp1 : Real.exp (-L * s) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith)
          have hC0 : 0 ≤ (2 * K + 1) / δ := by positivity
          exact mul_le_of_le_one_left hC0 hexp1
        · rw [indicator_of_notMem hs, mul_zero, mul_zero]

/-- Bound on the combined derivative + absorption integral for `coreExpRamp`. -/
theorem coreExpRamp_rhs_bound {C L δ : ℝ} {A ψ : ℝ → ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hA : ∀ s, 0 ≤ A s)
    (hb : ∀ s, deriv ψ s + L * ψ s ≤ C / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s)
    (hint : Integrable (fun s => (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
      (volume.restrict (Ioi (0 : ℝ)))) :
    ENNReal.ofReal (∫ s in Ioi (0 : ℝ), (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) ≤
      ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
  refine (ofReal_integral_le_lintegral' hint).trans ?_
  have hmeas : MeasurableSet (Ioo (0 : ℝ) (3 * δ)) := measurableSet_Ioo
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
      ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioo (0 : ℝ) (3 * δ)).indicator
          (fun s => ENNReal.ofReal (2 * C) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) s := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        by_cases hmem : s ∈ Icc δ (2 * δ)
        · have hIoo : s ∈ Ioo (0 : ℝ) (3 * δ) := ⟨hs0, by linarith [hmem.2]⟩
          rw [Set.indicator_of_mem hIoo, ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          have hd := hb s
          rw [Set.indicator_of_mem hmem] at hd
          have hr : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
            rw [← Real.rpow_add_one hs0.ne']; norm_num
          have hr0 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
          have hx : 0 ≤ s ^ (-3 / 2 : ℝ) * A s := mul_nonneg hr0 (hA s)
          have h1 : s ^ (-1 / 2 : ℝ) * A s ≤ 2 * δ * (s ^ (-3 / 2 : ℝ) * A s) := by
            rw [hr]
            nlinarith [mul_le_mul_of_nonneg_right hmem.2 hx]
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          calc (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)
              ≤ C / δ * 1 * (s ^ (-1 / 2 : ℝ) * A s) := mul_le_mul_of_nonneg_right hd hp
            _ ≤ C / δ * 1 * (2 * δ * (s ^ (-3 / 2 : ℝ) * A s)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * C * (s ^ (-3 / 2 : ℝ) * A s) := by field_simp
        · have hd := hb s
          rw [Set.indicator_of_notMem hmem, mul_zero] at hd
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          have : (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hd hp
          rw [ENNReal.ofReal_of_nonpos this]
          exact zero_le
    _ = ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
        have hinter : Ioo (0 : ℝ) (3 * δ) ∩ Ioi 0 = Ioo 0 (3 * δ) :=
          Set.inter_eq_left.2 (fun x hx => hx.1)
        rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas, hinter,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end UnforcedLeray.Short.IIIa
