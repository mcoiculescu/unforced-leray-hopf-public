import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.Chi
import UnforcedLeray.Short.PartIIa.Sub.N02

/-!
# Part II-a, task `PartII-a:N02/4/1` helper: the cut-off potential and its derivatives

For a complex potential `Φ` and the scale `ε`, `nzcoCut ε Φ = χ(√ε η) Φ`. The cutoff depends only on
`η`, so `∂_q` and `∂_s` of the product are the cut-off times the derivatives of `Φ`, and
`∂_η` picks up `χ'(√ε η) √ε Φ`. This file gives those identities and the two vector identities
`cgradC 0 Φ - cgradC ε (χ Φ)` and `streamC 0 Φ - streamC ε (χ Φ)` in coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The cut-off potential `χ(√ε η) Φ` (real scalar multiplication). -/
def nzcoCut (ε : ℝ) (Φ : Profile → ℂ) : Profile → ℂ := fun p => nzcoW ε p • Φ p

lemma nzcoCut_contDiff (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (nzcoCut ε Φ) :=
  (nzcoW_contDiff ε).smul hΦ

lemma nzcoCut_periodic (c ε : ℝ) {Φ : Profile → ℂ} (hΦ : QPeriodic c Φ) :
    QPeriodic c (nzcoCut ε Φ) := by
  intro p
  simp only [nzcoCut]
  rw [hΦ p]
  rfl

lemma nzcoCut_fderiv (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p v : Profile) :
    fderiv ℝ (nzcoCut ε Φ) p v = nzcoW ε p • fderiv ℝ Φ p v +
      (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε * v.2.2) • Φ p := by
  have hw : DifferentiableAt ℝ (nzcoW ε) p := ((nzcoW_contDiff ε).differentiable (by simp)) p
  have hf : DifferentiableAt ℝ Φ p := (hΦ.differentiable (by simp)) p
  have hs := hw.hasFDerivAt.smul hf.hasFDerivAt
  have hcut : nzcoCut ε Φ = nzcoW ε • Φ := rfl
  rw [hcut, hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, nzcoW_fderiv]

lemma nzcoCut_pdQ (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    pdQ (nzcoCut ε Φ) p = nzcoW ε p • pdQ Φ p := by
  unfold pdQ
  rw [nzcoCut_fderiv ε hΦ]
  simp

lemma nzcoCut_pdEta (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    pdEta (nzcoCut ε Φ) p = nzcoW ε p • pdEta Φ p +
      (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p := by
  unfold pdEta
  rw [nzcoCut_fderiv ε hΦ]
  simp

lemma nzcoCut_opS (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    opS (nzcoCut ε Φ) p = nzcoW ε p • opS Φ p := by
  simp only [opS, pdS]
  rw [nzcoCut_fderiv ε hΦ]
  simp
  ring

lemma nzcoCut_opK (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    opK (nzcoCut ε Φ) p = (2:ℝ) • (nzcoW ε p • opS Φ p) +
      p.2.2 • (nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p) := by
  simp only [opK]
  rw [nzcoCut_opS ε hΦ, nzcoCut_pdEta ε hΦ]

/-- The gradient difference in coordinates: `cgradC 0 Φ - cgradC ε (χΦ)`. -/
lemma nzco_cgrad_diff (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    cgradC 0 Φ p - cgradC ε (nzcoCut ε Φ) p =
      !₂[pdQ Φ p - (nzcoW ε p • pdQ Φ p - (ε : ℂ) * ((2:ℝ) • (nzcoW ε p • opS Φ p) +
          p.2.2 • (nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p))),
        pdEta Φ p - (nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p)] := by
  have h1 := nzcoCut_pdQ ε hΦ p
  have h2 := nzcoCut_pdEta ε hΦ p
  have h3 := nzcoCut_opK ε hΦ p
  simp only [cgradC]
  rw [h1, h2, h3]
  ext i
  fin_cases i <;> simp

/-- The stream difference in coordinates: `streamC ε (χΦ) - streamC 0 Φ`, with the sign of the
pointwise bound chosen so that the first component is `-(1-χ)∂_ηΦ - (χ')Φ`. -/
lemma nzco_stream_diff (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    streamC 0 Φ p - streamC ε (nzcoCut ε Φ) p =
      !₂[-pdEta Φ p - -(nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p),
        pdQ Φ p - (nzcoW ε p • pdQ Φ p - (ε : ℂ) * ((2:ℝ) • (nzcoW ε p • opS Φ p) +
          p.2.2 • (nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p)) +
          (ε : ℂ) * (nzcoW ε p • Φ p))] := by
  have h1 := nzcoCut_pdEta ε hΦ p
  have h2 := nzcoCut_pdQ ε hΦ p
  have h3 := nzcoCut_opK ε hΦ p
  simp only [streamC]
  rw [h1, h2, h3]
  simp only [nzcoCut]
  ext i
  fin_cases i <;> simp

end UnforcedLeray.Short.PartIIa
