import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_of
import UnforcedLeray.Units.B0610

/-!
# `SFCWeak`: the classical slice gradient is the weak cell gradient

Leaf of `PartIII-b:C/flatset/col/7/1/1/2/5` (source `shorter-proof-2026-11-02.tex` 1684-1689).
For a smooth `c`-periodic field `f` on the plane, the classical derivative `∂_j f` is the weak
cylinder derivative of `f` (integration by parts on the cell, no boundary terms by periodicity in
`q`, compact support of the test function in `η`).  Real and imaginary parts are handled by
`B0610.hasWeakCellDeriv_of_smooth`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (HasWeakCellDerivC)

/-- Integrability on the cell of a continuous complex function vanishing outside a compact set. -/
theorem cplx_cell_integrable {c : ℝ} {g : ℝ × ℝ → ℂ} (hg : Continuous g) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hv : ∀ x ∈ B0579.cell c, x ∉ K → g x = 0) :
    IntegrableOn g (B0579.cell c) :=
  (hg.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero (B0579.measurableSet_cell c)
    (fun x hx => hv x hx.1 hx.2)

/-- Integration by parts for a smooth `c`-periodic complex field against a cylinder test. -/
theorem cplx_ibp {c : ℝ} {j : Fin 2} {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => f x * (B0579.pd j ψ x : ℂ)) (B0579.cell c) ∧
    IntegrableOn (fun x => fderiv ℝ f x (B0579.dir j) * (ψ x : ℂ)) (B0579.cell c) ∧
    ∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ) =
      -∫ x in B0579.cell c, fderiv ℝ f x (B0579.dir j) * (ψ x : ℂ) := by
  obtain ⟨R, hR⟩ := hψ.vanish
  obtain ⟨R', hR'⟩ := (hψ.pd j).vanish
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous fun x => fderiv ℝ f x (B0579.dir j) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpc : Continuous fun x => (B0579.pd j ψ x : ℂ) :=
    Complex.continuous_ofReal.comp (hψ.pd j).continuous
  have hψc : Continuous fun x => (ψ x : ℂ) :=
    Complex.continuous_ofReal.comp hψ.continuous
  have I1 : IntegrableOn (fun x => f x * (B0579.pd j ψ x : ℂ)) (B0579.cell c) :=
    cplx_cell_integrable (hfc.mul hpc) (B0579.isCompact_box c R')
      (fun x hx hxK => by simp [hR' x hx hxK])
  have I2 : IntegrableOn (fun x => fderiv ℝ f x (B0579.dir j) * (ψ x : ℂ)) (B0579.cell c) :=
    cplx_cell_integrable (hdc.mul hψc) (B0579.isCompact_box c R)
      (fun x hx hxK => by simp [hR x hx hxK])
  refine ⟨I1, I2, ?_⟩
  -- real part and imaginary part of the field
  have hper_re : ∀ x : ℝ × ℝ, (fun y => (f y).re) (x.1 + c, x.2) = (fun y => (f y).re) x := by
    intro x; simp only [hper x]
  have hper_im : ∀ x : ℝ × ℝ, (fun y => (f y).im) (x.1 + c, x.2) = (fun y => (f y).im) x := by
    intro x; simp only [hper x]
  have hu : ContDiff ℝ ∞ (fun y => (f y).re) :=
    Complex.reCLM.contDiff.comp hf
  have hv : ContDiff ℝ ∞ (fun y => (f y).im) :=
    Complex.imCLM.contDiff.comp hf
  have hdre : ∀ x : ℝ × ℝ, (fderiv ℝ f x (B0579.dir j)).re
      = B0579.pd j (fun y => (f y).re) x := by
    intro x
    have h1 : HasFDerivAt (fun y => (f y).re) (Complex.reCLM.comp (fderiv ℝ f x)) x :=
      Complex.reCLM.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt
    simp only [B0579.pd, h1.fderiv, ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have hdim : ∀ x : ℝ × ℝ, (fderiv ℝ f x (B0579.dir j)).im
      = B0579.pd j (fun y => (f y).im) x := by
    intro x
    have h1 : HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x :=
      Complex.imCLM.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt
    simp only [B0579.pd, h1.fderiv, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  have hre_ibp := (B0610.hasWeakCellDeriv_of_smooth hu hper_re j) ψ hψ
  have him_ibp := (B0610.hasWeakCellDeriv_of_smooth hv hper_im j) ψ hψ
  simp only [← hdre, ← hdim] at hre_ibp him_ibp
  -- take real and imaginary parts of both sides
  have hL_re := integral_re I1
  have hL_im := integral_im I1
  have hG_re := integral_re I2
  have hG_im := integral_im I2
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
    at hL_re hL_im hG_re hG_im
  apply Complex.ext
  · rw [Complex.neg_re, ← hL_re, ← hG_re]
    exact hre_ibp
  · rw [Complex.neg_im, ← hL_im, ← hG_im]
    exact him_ibp

/-- The complex classical derivative of a smooth periodic field is its weak cell derivative. -/
theorem cplx_weak {c : ℝ} {j : Fin 2} {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) :
    HasWeakCellDerivC c j f (fun x => fderiv ℝ f x (B0579.dir j)) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => (cplx_ibp hf hper ψ hψ).2.2⟩
  exact ⟨(cplx_ibp hf hper ψ hψ).1, (cplx_ibp hf hper ψ hψ).2.1⟩

theorem sfcWeak : SFCWeak := by
  intro c b hb s hs i j
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ × ℝ => b (s, x) i) := by
    have h1 : ContDiffOn ℝ ∞ (fun p : Chart => b p i) (Ioi (0 : ℝ) ×ˢ univ) :=
      (hb.2.1 i).of_le le_rfl
    have h2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((s, x) : Chart)) :=
      contDiff_const.prodMk contDiff_id
    exact h1.comp_contDiff h2 (fun x => ⟨hs, mem_univ _⟩)
  have hper : ∀ x : ℝ × ℝ, b (s, (x.1 + c, x.2)) i = b (s, x) i := by
    intro x
    have h := hb.2.2.1 s x.1 x.2 hs
    simp only [h]
  exact cplx_weak hsmooth hper

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
