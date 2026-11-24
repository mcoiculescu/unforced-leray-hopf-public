import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff.Ftc
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff.Tonelli

/-!
# `PartIII-a:T21/2/2/org-higher-reg/1`: differentiability of the adjoint in `X_{-m,c}`

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073.

`adjXDiff`: for an adjoint flow `φ` (`IsAdjointFlow`), the difference quotients of `∂^wφ(r)` in
`X_{-m,c}` converge to `∂^w∂_rφ(r)`, for `w` of length at most one, at every age `r ∈ (t, s)`.

Proof (no pointwise majorant, the cell is an infinite strip):
* `ftc_adjSpatial` (`Ftc.lean`): pointwise in `x`, `∂^wφ(r') - ∂^wφ(r) = ∫_r^{r'} ∂^w∂_rφ(ρ)dρ`.
* the difference quotient is the average `(r' - r)⁻¹ ∫_r^{r'} G_ρ dρ` of `G_ρ = ∂^w∂_rφ(ρ) - ∂^w∂_rφ(r)`.
* `eLpNorm_avg_le` (`Tonelli.lean`, Cauchy-Schwarz in `ρ` and Tonelli in `x`): its `X` norm is at
  most `η` as soon as `‖G_ρ‖_X ≤ η` for all `ρ` between `r` and `r'`, which is the continuity
  `higherCont` of `∂^w∂_rφ` in `X_{-m,c}` (second conjunct of `AdjHigherCont`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

theorem dist_uIcc_le' {r r' ρ : ℝ} (h : ρ ∈ uIcc r r') : dist ρ r ≤ dist r' r := by
  have h' : min r r' ≤ ρ ∧ ρ ≤ max r r' := h
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total r r' with hh | hh
  · rw [min_eq_left hh, max_eq_right hh] at h'
    rw [abs_of_nonneg (by linarith [h'.1] : (0 : ℝ) ≤ ρ - r),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ r' - r)]
    linarith [h'.2]
  · rw [min_eq_right hh, max_eq_left hh] at h'
    rw [abs_of_nonpos (by linarith [h'.2] : ρ - r ≤ 0), abs_of_nonpos (by linarith : r' - r ≤ 0)]
    linarith [h'.1]

theorem uIcc_sub_strip' {t s r r' : ℝ} (hr : r ∈ Ioo t s) (hr' : r' ∈ Ioo t s) :
    uIcc r r' ⊆ Ioo t s := by
  rcases le_total r r' with h | h
  · rw [uIcc_of_le h]; exact Icc_subset_Ioo hr.1 hr'.2
  · rw [uIcc_of_ge h]; exact Icc_subset_Ioo hr'.1 hr.2

/-- **`PartIII-a:T21/2/2/org-higher-reg/1`** (SP 3060-3073): the difference quotients of
`∂^wφ` converge in `X_{-m,c}` to `∂^w∂_rφ`, for `|w| ≤ 1`, at every age `r ∈ (t, s)`. -/
theorem adjXDiff (m : ℝ) : UnforcedLeray.Short.IIIa.AdjXDiff m := by
  intro ν hν tr t s ht0 hts g φ hφ r hr w hw
  have hj : ContDiffOn ℝ ∞ (jF φ) (Ioo t s ×ˢ univ) :=
    hφ.jointSmooth.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (adjDt t s φ p.1) p.2)
      (Ioo t s ×ˢ univ) :=
    continuousOn_adjSpatial hj w hw
  -- the continuity of the age-`r` slice
  have hHr : ContinuousOn (fun x : ℝ × ℝ => adjSpatial w (adjDt t s φ r) x) univ := by
    have hι : Continuous (fun x : ℝ × ℝ => ((r, x) : ℝ × (ℝ × ℝ))) :=
      continuous_const.prodMk continuous_id
    exact hcont.comp hι.continuousOn (fun x _ => ⟨hr, mem_univ x⟩)
  set Gf : ℝ → ℝ × ℝ → ℂ := fun ρ x => adjSpatial w (adjDt t s φ ρ) x -
    adjSpatial w (adjDt t s φ r) x with hGf_def
  have hG : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => Gf p.1 p.2) (Ioo t s ×ˢ univ) := by
    apply ContinuousOn.sub hcont
    exact hHr.comp continuous_snd.continuousOn (fun p _ => mem_univ p.2)
  -- the difference quotient is the average of `Gf`
  have hD : ∀ r' ∈ Ioo t s, r' ≠ r →
      ((r' - r)⁻¹ : ℝ) • (adjSpatial w (φ r') - adjSpatial w (φ r)) -
          adjSpatial w (adjDt t s φ r) =
        fun x => ((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', Gf ρ x := by
    intro r' hr' hne
    funext x
    have hcx : ContinuousOn (fun ρ => adjSpatial w (adjDt t s φ ρ) x) (uIcc r r') := by
      have hι : Continuous (fun ρ : ℝ => ((ρ, x) : ℝ × (ℝ × ℝ))) :=
        continuous_id.prodMk continuous_const
      exact hcont.comp hι.continuousOn
        (fun ρ hρ => ⟨uIcc_sub_strip' hr hr' hρ, mem_univ x⟩)
    have hint1 : IntervalIntegrable (fun ρ => adjSpatial w (adjDt t s φ ρ) x) volume r r' :=
      hcx.intervalIntegrable
    have hint2 : IntervalIntegrable (fun _ : ℝ => adjSpatial w (adjDt t s φ r) x) volume r r' :=
      intervalIntegrable_const
    have hsplit : ∫ ρ in r..r', Gf ρ x =
        (∫ ρ in r..r', adjSpatial w (adjDt t s φ ρ) x) -
          ∫ _ in r..r', adjSpatial w (adjDt t s φ r) x :=
      intervalIntegral.integral_sub hint1 hint2
    have hF := ftc_adjSpatial hj hr hr' w hw x
    rw [hsplit, intervalIntegral.integral_const, ← hF]
    simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
    push_cast
    have hz : ((r' : ℂ) - (r : ℂ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
    linear_combination (adjSpatial w (adjDt t s φ r) x) * (inv_mul_cancel₀ hz)
  -- the target function, with the `X` norm
  have hGt : Tendsto (fun ρ => xNorm (ν ^ (-2 : ℝ)) (-m) (Gf ρ)) (𝓝[Ico t s] r) (𝓝 0) :=
    ((hφ.higherCont r (Ioo_subset_Ico_self hr) w).2 hw).2
  have hSF : SFinite (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    unfold B0579.cellMeasure
    infer_instance
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := ENNReal.tendsto_nhds_zero.1 hGt ε hε
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  have hA : ∀ᶠ r' in 𝓝 r, r' ∈ Ioo t s := Ioo_mem_nhds hr.1 hr.2
  have hB : ∀ᶠ r' in 𝓝 r, dist r' r < δ := Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun y hy => hy⟩
  have hR : ∀ᶠ r' in 𝓝[≠] r, r' ∈ Ioo t s ∧ dist r' r < δ :=
    nhdsWithin_le_nhds (hA.and hB)
  filter_upwards [hR, self_mem_nhdsWithin] with r' hr'1 hr'2
  have hne : r' ≠ r := Set.mem_compl_singleton_iff.1 hr'2
  have hr'Ioo : r' ∈ Ioo t s := hr'1.1
  have hdist : dist r' r < δ := hr'1.2
  rw [hD r' hr'Ioo hne]
  unfold xNorm
  apply eLpNorm_avg_le (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) r r' (Ne.symm hne) Gf
    (hG.mono (prod_mono (uIcc_sub_strip' hr hr'Ioo) subset_rfl)) ε
  intro ρ hρ
  have hρS : ρ ∈ Ioo t s := uIcc_sub_strip' hr hr'Ioo (uIoc_subset_uIcc hρ)
  have hdis : dist ρ r < δ := lt_of_le_of_lt (dist_uIcc_le' (uIoc_subset_uIcc hρ)) hdist
  exact hδP hdis (Ioo_subset_Ico_self hρS)

end UnforcedLeray.Short.IIIa
