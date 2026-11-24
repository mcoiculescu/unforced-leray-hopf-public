import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff

/-!
# `PartIII-a:T21/2/2`, helper: the pointwise fundamental theorem of calculus in the age

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073.

For a field `ψ : ℝ → ℝ × ℝ → ℂ` whose joint map `jF ψ (ρ, x) = ψ ρ x` is smooth on the open
strip `Ioo a b ×ˢ univ`, the slices `ρ ↦ ψ ρ x` and `x ↦ ψ ρ x` are differentiable, the age
derivative `adjDt` is the partial derivative of `jF ψ` in the first slot, and the mixed partials
commute (`ContDiffAt.isSymmSndFDerivAt`). Consequently, pointwise in `x`,
`adjSpatial w (ψ r') x - adjSpatial w (ψ r) x = ∫ ρ in r..r', adjSpatial w (adjDt ρ) x` for
words `w` of length at most one (no majorant is used).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- The joint field `(ρ, x) ↦ ψ ρ x`. -/
def jF (ψ : ℝ → ℝ × ℝ → ℂ) : ℝ × (ℝ × ℝ) → ℂ := fun p => ψ p.1 p.2

theorem isOpen_strip (a b : ℝ) : IsOpen (Ioo a b ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioo.prod isOpen_univ

section Pointwise

variable {a b : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}

theorem contDiffAt_jF (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo a b) (x : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (jF ψ) (ρ, x) :=
  hj.contDiffAt (IsOpen.mem_nhds (isOpen_strip a b) ⟨hρ, mem_univ x⟩)

/-- The first slice derivative of `jF ψ` is itself `C¹` on the strip. -/
theorem contDiffOn_fderiv_jF (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) :
    ContDiffOn ℝ 1 (fderiv ℝ (jF ψ)) (Ioo a b ×ˢ univ) :=
  hj.fderiv_of_isOpen (isOpen_strip a b) (m := 1) (by simp)

/-- The second derivative of `jF ψ` is continuous on the strip. -/
theorem continuousOn_fderiv_fderiv_jF (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) :
    ContinuousOn (fderiv ℝ (fderiv ℝ (jF ψ))) (Ioo a b ×ˢ univ) :=
  ((contDiffOn_fderiv_jF hj).fderiv_of_isOpen (isOpen_strip a b) (m := 0) (by simp)).continuousOn

/-- Slice derivative in `x`: `fderiv (jF ψ)` restricted to the slice `y ↦ (ρ, y)`. -/
theorem hasFDerivAt_slice_jF (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo a b) (x : ℝ × ℝ) :
    HasFDerivAt (ψ ρ)
      ((fderiv ℝ (jF ψ) (ρ, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := by
  have hd : HasFDerivAt (jF ψ) (fderiv ℝ (jF ψ) (ρ, x)) (ρ, x) :=
    ((contDiffAt_jF hj hρ x).differentiableAt (by simp)).hasFDerivAt
  have hι : HasFDerivAt (fun y : ℝ × ℝ => ((ρ, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const ρ x).prodMk (hasFDerivAt_id x)
  exact hd.comp x hι

theorem pdCx_slice_eq (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo a b) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (ψ ρ) x = fderiv ℝ (jF ψ) (ρ, x) ((0 : ℝ), B0579.dir k) := by
  unfold pdCx
  rw [(hasFDerivAt_slice_jF hj hρ x).fderiv]
  simp

/-- The age derivative of `ψ` at an interior age is the first partial of `jF ψ`. -/
theorem hasDerivAt_jF (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo a b) (x : ℝ × ℝ) :
    HasDerivAt (fun r => ψ r x) (fderiv ℝ (jF ψ) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ))) ρ := by
  have hd : HasFDerivAt (jF ψ) (fderiv ℝ (jF ψ) (ρ, x)) (ρ, x) :=
    ((contDiffAt_jF hj hρ x).differentiableAt (by simp)).hasFDerivAt
  have hι : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
  exact hd.comp_hasDerivAt ρ hι

theorem adjDt_eq_fderiv (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo a b) (x : ℝ × ℝ) :
    adjDt a b ψ ρ x = fderiv ℝ (jF ψ) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) := by
  unfold adjDt
  rw [derivWithin_of_mem_nhds (Ico_mem_nhds hρ.1 hρ.2)]
  exact (hasDerivAt_jF hj hρ x).deriv

theorem continuousOn_fderiv_jF_slice (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) (x : ℝ × ℝ)
    {I : Set ℝ} (hI : I ⊆ Ioo a b) (v : ℝ × (ℝ × ℝ)) :
    ContinuousOn (fun ρ => fderiv ℝ (jF ψ) (ρ, x) v) I := by
  have hF : ContinuousOn (fderiv ℝ (jF ψ)) (Ioo a b ×ˢ univ) :=
    (contDiffOn_fderiv_jF hj).continuousOn
  have hc : ContinuousOn (fun ρ : ℝ => ((ρ, x) : ℝ × (ℝ × ℝ))) I :=
    (continuous_id.prodMk continuous_const).continuousOn
  have h := hF.comp hc (fun ρ hρ => ⟨hI hρ, mem_univ x⟩)
  exact (h.clm_apply continuousOn_const)

/-- The second slice derivative: `ρ ↦ ∂_v jF(ρ, x)` has derivative `∂_ρ∂_v jF`. -/
theorem hasDerivAt_fderiv_jF_slice (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo a b) (x : ℝ × ℝ) (v : ℝ × (ℝ × ℝ)) :
    HasDerivAt (fun r => fderiv ℝ (jF ψ) (r, x) v)
      (fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) v) ρ := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (jF ψ)) (ρ, x) :=
    ((contDiffOn_fderiv_jF hj).contDiffAt
      (IsOpen.mem_nhds (isOpen_strip a b) ⟨hρ, mem_univ x⟩)).differentiableAt (by simp)
  have hι : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
  have hc : HasDerivAt (fun r : ℝ => fderiv ℝ (jF ψ) (r, x))
      (fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ))) ρ :=
    hdiff.hasFDerivAt.comp_hasDerivAt ρ hι
  simpa using hc.clm_apply (hasDerivAt_const ρ v)

/-- Symmetry of the second derivative of `jF ψ` on the strip. -/
theorem symm_jF (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) {ρ : ℝ} (hρ : ρ ∈ Ioo a b)
    (x : ℝ × ℝ) (v w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) v w = fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) w v := by
  have hs : IsSymmSndFDerivAt ℝ (jF ψ) (ρ, x) :=
    (contDiffAt_jF hj hρ x).isSymmSndFDerivAt (by simp)
  exact hs v w

/-- `∂_k (∂_ρ ψ)(ρ, ·)` is the second derivative `∂_ρ ∂_k` of `jF ψ`. -/
theorem pdCx_adjDt_eq (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) {ρ : ℝ}
    (hρ : ρ ∈ Ioo a b) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (adjDt a b ψ ρ) x =
      fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) ((0 : ℝ), B0579.dir k) ((1 : ℝ), (0 : ℝ × ℝ)) := by
  have hfun : adjDt a b ψ ρ = fun y => fderiv ℝ (jF ψ) (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun y => adjDt_eq_fderiv hj hρ y
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (jF ψ)) (ρ, x) :=
    ((contDiffOn_fderiv_jF hj).contDiffAt
      (IsOpen.mem_nhds (isOpen_strip a b) ⟨hρ, mem_univ x⟩)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ (jF ψ) q ((1 : ℝ), (0 : ℝ × ℝ)))
      ((fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x)).flip ((1 : ℝ), (0 : ℝ × ℝ))) (ρ, x) := by
    simpa using hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : ℝ × ℝ)) (ρ, x))
  have hs : HasFDerivAt (fun y : ℝ × ℝ => ((ρ, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const ρ x).prodMk (hasFDerivAt_id x)
  have hG : HasFDerivAt (fun y : ℝ × ℝ => fderiv ℝ (jF ψ) (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ)))
      (((fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x)).flip ((1 : ℝ), (0 : ℝ × ℝ))).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := hc.comp x hs
  unfold pdCx
  rw [hfun, hG.fderiv]
  simp

/-- The age-FTC at fixed `x`. -/
theorem ftc_zero (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) {r r' : ℝ}
    (hr : r ∈ Ioo a b) (hr' : r' ∈ Ioo a b) (x : ℝ × ℝ) :
    ψ r' x - ψ r x = ∫ ρ in r..r', adjDt a b ψ ρ x := by
  have hsub : uIcc r r' ⊆ Ioo a b := by
    rcases le_total r r' with h | h
    · rw [uIcc_of_le h]; exact Icc_subset_Ioo hr.1 hr'.2
    · rw [uIcc_of_ge h]; exact Icc_subset_Ioo hr'.1 hr.2
  have hderiv : ∀ ρ ∈ uIcc r r', HasDerivAt (fun σ => ψ σ x) (adjDt a b ψ ρ x) ρ := by
    intro ρ hρ
    rw [adjDt_eq_fderiv hj (hsub hρ) x]
    exact hasDerivAt_jF hj (hsub hρ) x
  have hint : IntervalIntegrable (fun ρ => adjDt a b ψ ρ x) volume r r' := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_fderiv_jF_slice hj x hsub _).congr
      (fun ρ hρ => adjDt_eq_fderiv hj (hsub hρ) x)
  exact (integral_eq_sub_of_hasDerivAt hderiv hint).symm

/-- The age-FTC for `∂_k` at fixed `x`. -/
theorem ftc_one (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) (k : Fin 2) {r r' : ℝ}
    (hr : r ∈ Ioo a b) (hr' : r' ∈ Ioo a b) (x : ℝ × ℝ) :
    pdCx k (ψ r') x - pdCx k (ψ r) x = ∫ ρ in r..r', pdCx k (adjDt a b ψ ρ) x := by
  have hsub : uIcc r r' ⊆ Ioo a b := by
    rcases le_total r r' with h | h
    · rw [uIcc_of_le h]; exact Icc_subset_Ioo hr.1 hr'.2
    · rw [uIcc_of_ge h]; exact Icc_subset_Ioo hr'.1 hr.2
  have hderiv : ∀ ρ ∈ uIcc r r', HasDerivAt (fun σ => pdCx k (ψ σ) x)
      (pdCx k (adjDt a b ψ ρ) x) ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have h1 := hasDerivAt_fderiv_jF_slice hj hρ' x ((0 : ℝ), B0579.dir k)
    have hsy := symm_jF hj hρ' x ((1 : ℝ), (0 : ℝ × ℝ)) ((0 : ℝ), B0579.dir k)
    rw [pdCx_adjDt_eq hj hρ' k x]
    rw [hsy] at h1
    refine h1.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioo_mem_nhds hρ'.1 hρ'.2)
      (fun σ hσ => pdCx_slice_eq hj hσ k x)
  have hcont : ContinuousOn (fun ρ => pdCx k (adjDt a b ψ ρ) x) (uIcc r r') := by
    have hc2 : ContinuousOn (fun ρ : ℝ => ((ρ, x) : ℝ × (ℝ × ℝ))) (uIcc r r') :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hH := (continuousOn_fderiv_fderiv_jF hj).comp hc2
      (fun ρ hρ => ⟨hsub hρ, mem_univ x⟩)
    have h1 : ContinuousOn (fun ρ => fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) ((0 : ℝ), B0579.dir k))
        (uIcc r r') := hH.clm_apply continuousOn_const
    have h2 : ContinuousOn (fun ρ => fderiv ℝ (fderiv ℝ (jF ψ)) (ρ, x) ((0 : ℝ), B0579.dir k)
        ((1 : ℝ), (0 : ℝ × ℝ))) (uIcc r r') := h1.clm_apply continuousOn_const
    exact h2.congr (fun ρ hρ => pdCx_adjDt_eq hj (hsub hρ) k x)
  exact (integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable).symm

/-- **Pointwise FTC for `adjSpatial`** (words of length at most one). -/
theorem ftc_adjSpatial (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) {r r' : ℝ}
    (hr : r ∈ Ioo a b) (hr' : r' ∈ Ioo a b) (w : List (Fin 2)) (hw : w.length ≤ 1) (x : ℝ × ℝ) :
    adjSpatial w (ψ r') x - adjSpatial w (ψ r) x =
      ∫ ρ in r..r', adjSpatial w (adjDt a b ψ ρ) x := by
  rcases w with _ | ⟨k, _ | ⟨k', w⟩⟩
  · exact ftc_zero hj hr hr' x
  · exact ftc_one hj k hr hr' x
  · simp at hw

/-- Joint continuity of `(ρ, x) ↦ ∂^w ∂_ρ ψ` on the strip (words of length at most one). -/
theorem continuousOn_adjSpatial (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ))
    (w : List (Fin 2)) (hw : w.length ≤ 1) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (adjDt a b ψ p.1) p.2)
      (Ioo a b ×ˢ univ) := by
  rcases w with _ | ⟨k, _ | ⟨k', w⟩⟩
  · show ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjDt a b ψ p.1 p.2) (Ioo a b ×ˢ univ)
    refine ContinuousOn.congr ?_ (fun p hp => adjDt_eq_fderiv hj hp.1 p.2)
    exact (contDiffOn_fderiv_jF hj).continuousOn.clm_apply continuousOn_const
  · show ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (adjDt a b ψ p.1) p.2) (Ioo a b ×ˢ univ)
    refine ContinuousOn.congr ?_ (fun p hp => pdCx_adjDt_eq hj hp.1 k p.2)
    exact ((continuousOn_fderiv_fderiv_jF hj).clm_apply continuousOn_const).clm_apply
      continuousOn_const
  · simp at hw

end Pointwise

end UnforcedLeray.Short.IIIa
