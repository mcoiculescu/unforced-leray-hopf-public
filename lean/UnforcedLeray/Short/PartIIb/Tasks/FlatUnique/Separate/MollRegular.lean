import UnforcedLeray.Short.PartIIb.Sub.T11_6

/-!
# Leaf `MollRegular`: the tensor mollification of a cut-off is `C^∞`

Proves `MollRegular` (defined in `Sub/T11_6.lean`) by identifying `mollC` with the convolution
`cutC δ g ⋆[mrgL, volume] tensorK ρ₁ ρ₂` and applying Mathlib's convolution differentiability
lemmas. Classical mollification; the source of record is
`the November 2 reference manuscript`, SP 2618 (free uniqueness step), which does
not write this argument.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Real scalar multiplication `z ↦ r • z` as a bilinear map `ℂ →L[ℝ] ℝ →L[ℝ] ℂ`
(first argument the complex value, second the real scalar). -/
def mrgL : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

theorem mrgL_apply (z : ℂ) (r : ℝ) : mrgL z r = (r : ℂ) * z := by
  simp [mrgL, Complex.real_smul]

/-- Lebesgue measure on `ℝ × ℝ` is an additive Haar measure (instance search does not see the
defeq `volume = volume.prod volume`, so it is stated explicitly, as in `Lib/Cylinder/Basic.lean`). -/
instance mrg_isAddHaarMeasure_volume_plane :
    Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on the chart `Coord = ℝ × (ℝ × ℝ)` is an additive Haar measure. -/
instance mrg_isAddHaarMeasure_volume_coord :
    Measure.IsAddHaarMeasure (volume : Measure Coord) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The tensor kernel `ρ₁(y.1) ρ₂(y.2)` is smooth when `ρ₁` and `ρ₂` are. -/
theorem mrg_tensorK_contDiff (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (h : IsMollKer δ ρ₁ ρ₂) :
    ContDiff ℝ ∞ (tensorK ρ₁ ρ₂) := by
  unfold tensorK
  exact (h.smooth₁.comp contDiff_fst).mul (h.smooth₂.comp contDiff_snd)

/-- The tensor kernel vanishes outside the compact box `[-δ, δ] × ([-δ, δ] × [-δ, δ])`. -/
theorem mrg_tensorK_hasCompactSupport (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ)
    (h : IsMollKer δ ρ₁ ρ₂) : HasCompactSupport (tensorK ρ₁ ρ₂) := by
  refine HasCompactSupport.intro
    (K := Icc (-δ) δ ×ˢ (Icc (-δ) δ ×ˢ Icc (-δ) δ))
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) ?_
  intro y hy
  by_cases h1 : δ < |y.1|
  · simp [tensorK, h.supp₁ y.1 h1]
  · have h2 : δ < |y.2.1| ∨ δ < |y.2.2| := by
      by_contra hc
      simp only [not_or, not_lt] at hc
      apply hy
      exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp (not_lt.mp h1)),
        Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp hc.1), Set.mem_Icc.mpr (abs_le.mp hc.2)⟩⟩
    simp [tensorK, h.supp₂ y.2 h2]

/-- **Leaf `mollRegular`.** The tensor mollification of the cut-off `cutC δ g` is `C^∞`, and its
derivative in the direction `v` is the convolution of `cutC δ g` against the directional derivative
of the tensor kernel. -/
theorem mollRegular : UnforcedLeray.Short.IIb.MollRegular := by
  intro g δ ρ₁ ρ₂ _hδ hK hloc
  have hTK : ContDiff ℝ ∞ (tensorK ρ₁ ρ₂) := mrg_tensorK_contDiff δ ρ₁ ρ₂ hK
  have hTK1 : ContDiff ℝ 1 (tensorK ρ₁ ρ₂) := hTK.of_le (by simp)
  have hcs : HasCompactSupport (tensorK ρ₁ ρ₂) := mrg_tensorK_hasCompactSupport δ ρ₁ ρ₂ hK
  have hcont : Continuous (fderiv ℝ (tensorK ρ₁ ρ₂)) := hTK1.continuous_fderiv (by simp)
  have hfun : mollC δ ρ₁ ρ₂ g = convolution (cutC δ g) (tensorK ρ₁ ρ₂) mrgL volume := by
    funext p
    rw [convolution_def]
    simp only [mollC, mollG, tensorK, mrgL_apply, Prod.fst_sub, Prod.snd_sub]
  refine ⟨?_, fun p v => ?_⟩
  · rw [hfun]
    exact HasCompactSupport.contDiff_convolution_right mrgL hcs hloc hTK
  · have hd := hcs.hasFDerivAt_convolution_right mrgL hloc hTK1 p
    rw [hfun, hd.fderiv, convolution_precompR_apply mrgL hloc (hcs.fderiv ℝ) hcont p v]
    simp only [convolution_def, mrgL_apply]

end UnforcedLeray.Short.IIb
