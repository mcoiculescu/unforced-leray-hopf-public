import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1_3

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/3/1` (`commCpdMul`): Leibniz rule for `cpdC` with the
cutoff factor `f(η/L)`.

Source: `the November 2 reference manuscript` lines 1923-1927.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem commCdir_snd (j : Fin 3) : (cdir j).2.2 = if j = 2 then 1 else 0 := by
  fin_cases j <;> simp [cdir]

theorem commEtaHas (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ) (y : Coord) :
    HasFDerivAt (fun z : Coord => f (z.2.2 / L))
      (deriv f (y.2.2 / L) •
        (L⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) y := by
  have hd : HasDerivAt f (deriv f (y.2.2 / L)) (y.2.2 / L) :=
    ((hf.differentiable (by simp)) _).hasDerivAt
  have h2 : HasFDerivAt (fun z : Coord => z.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_snd).comp y hasFDerivAt_snd
  have hfun : (fun z : Coord => z.2.2 / L) = fun z : Coord => z.2.2 * L⁻¹ := by
    funext z
    rw [div_eq_mul_inv]
  have hg : HasFDerivAt (fun z : Coord => z.2.2 / L)
      (L⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) y := by
    rw [hfun]
    exact h2.mul_const L⁻¹
  exact hd.comp_hasFDerivAt y hg

theorem commEtaFD (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ) (y v : Coord) :
    fderiv ℝ (fun z : Coord => f (z.2.2 / L)) y v = deriv f (y.2.2 / L) * (v.2.2 / L) := by
  rw [(commEtaHas f hf L y).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  show deriv f (y.2.2 / L) * (L⁻¹ * v.2.2) = deriv f (y.2.2 / L) * (v.2.2 / L)
  ring

theorem commPHas (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ) (y : Coord) :
    fderiv ℝ (fun z : Coord => ((f (z.2.2 / L) : ℝ) : ℂ)) y =
      Complex.ofRealCLM.comp (fderiv ℝ (fun z : Coord => f (z.2.2 / L)) y) := by
  rw [(commEtaHas f hf L y).fderiv]
  exact (Complex.ofRealCLM.hasFDerivAt.comp y (commEtaHas f hf L y)).fderiv

theorem commPd (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ) (y : Coord) (j : Fin 3) :
    fderiv ℝ (fun z : Coord => ((f (z.2.2 / L) : ℝ) : ℂ)) y (cdir j) =
      if j = 2 then (((L⁻¹ * deriv f (y.2.2 / L) : ℝ)) : ℂ) else 0 := by
  rw [commPHas f hf L y, ContinuousLinearMap.comp_apply, commEtaFD f hf L y,
    Complex.ofRealCLM_apply, commCdir_snd j]
  split_ifs with h
  · push_cast
    ring
  · simp

theorem commCpdMul (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ) (Ψ : Coord → ℂ) (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3) : cpdC j (fun y : Coord => ((f (y.2.2 / L) : ℝ) : ℂ) * Ψ y) = fun y : Coord => ((f (y.2.2 / L) : ℝ) : ℂ) * cpdC j Ψ y + (if j = 2 then (((L⁻¹ * deriv f (y.2.2 / L) : ℝ)) : ℂ) else 0) * Ψ y := by
  funext y
  have hPsm : ContDiff ℝ ∞ (fun z : Coord => ((f (z.2.2 / L) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.comp ((contDiff_snd.comp contDiff_snd).div_const L))
  have hPdiff : DifferentiableAt ℝ (fun z : Coord => ((f (z.2.2 / L) : ℝ) : ℂ)) y :=
    (hPsm.differentiable (by simp)) y
  have hΨdiff : DifferentiableAt ℝ Ψ y := (hΨ.differentiable (by simp)) y
  have hmul : fderiv ℝ (fun z : Coord => ((f (z.2.2 / L) : ℝ) : ℂ) * Ψ z) y =
      ((f (y.2.2 / L) : ℝ) : ℂ) • fderiv ℝ Ψ y +
        Ψ y • fderiv ℝ (fun z : Coord => ((f (z.2.2 / L) : ℝ) : ℂ)) y :=
    fderiv_mul hPdiff hΨdiff
  simp only [cpdC]
  rw [hmul]
  simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]
  rw [commPd f hf L y j]
  ring
