import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Calculus of the regularised cylinder Green function (`RegKerCalc`)

Source `the November 2 reference manuscript` 1676.  `Γ_ε = (4π)⁻¹ log (D + ε)` is smooth
and `c`-periodic in `q` for `ε > 0`; `∂_q Γ_ε = K₀^ε`, `∂_η Γ_ε = K₁^ε` (`cylKerReg`), and
`ΔΓ_ε = ρ_ε` (`cylRho`), by differentiating the quotients and using `sin² + sinh² = cosh² - cos²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Slice derivative in `q` determines `pd2 0`. -/
lemma pd2_zero_eq_of_hasDerivAt (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (d : ℝ)
    (hg : DifferentiableAt ℝ g y) (h : HasDerivAt (fun t : ℝ => g (t, y.2)) d y.1) :
    pd2 0 g y = d := by
  have hl : HasDerivAt (fun t : ℝ => ((t, y.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id' y.1).prodMk (hasDerivAt_const y.1 y.2)
  have hc : HasFDerivAt g (fderiv ℝ g y) (y.1, y.2) := hg.hasFDerivAt
  have h2 := hc.comp_hasDerivAt y.1 hl
  have hdir : dir2 0 = ((1 : ℝ), (0 : ℝ)) := by simp [dir2]
  unfold pd2
  rw [hdir]
  exact (h.unique h2).symm

/-- Slice derivative in `η` determines `pd2 1`. -/
lemma pd2_one_eq_of_hasDerivAt (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (d : ℝ)
    (hg : DifferentiableAt ℝ g y) (h : HasDerivAt (fun t : ℝ => g (y.1, t)) d y.2) :
    pd2 1 g y = d := by
  have hl : HasDerivAt (fun t : ℝ => ((y.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id' y.2)
  have hc : HasFDerivAt g (fderiv ℝ g y) (y.1, y.2) := hg.hasFDerivAt
  have h2 := hc.comp_hasDerivAt y.2 hl
  have hdir : dir2 1 = ((0 : ℝ), (1 : ℝ)) := by simp [dir2]
  unfold pd2
  rw [hdir]
  exact (h.unique h2).symm

lemma cylDen_add_pos (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) : 0 < cylDen c y + ε := by
  unfold cylDen
  have h1 := Real.one_le_cosh (cylFreq c * y.2)
  have h2 := Real.cos_le_one (cylFreq c * y.1)
  linarith

lemma den_ne (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε ≠ 0 :=
  (cylDen_add_pos c ε hε y).ne'

lemma contDiff_den_eps (c ε : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) :=
  ((Real.contDiff_cosh.comp (contDiff_const.mul contDiff_snd)).sub
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_fst))).add contDiff_const

lemma contDiff_cylGreenReg (c ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (cylGreenReg c ε) := by
  unfold cylGreenReg cylDen
  exact contDiff_const.mul ((contDiff_den_eps c ε).log (fun y => den_ne c ε hε y))

lemma cylKerReg_zero_eq (c ε : ℝ) :
    cylKerReg c ε 0 = fun y : ℝ × ℝ =>
      cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * y.1) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) := by
  funext y
  simp [cylKerReg, cylNum, cylDen]

lemma cylKerReg_one_eq (c ε : ℝ) :
    cylKerReg c ε 1 = fun y : ℝ × ℝ =>
      cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) := by
  funext y
  simp [cylKerReg, cylNum, cylDen]

lemma contDiff_cylKerReg_zero (c ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (cylKerReg c ε 0) := by
  rw [cylKerReg_zero_eq]
  exact (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst))).div
    (contDiff_den_eps c ε) (fun y => den_ne c ε hε y)

lemma contDiff_cylKerReg_one (c ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (cylKerReg c ε 1) := by
  rw [cylKerReg_one_eq]
  exact (contDiff_const.mul (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_snd))).div
    (contDiff_den_eps c ε) (fun y => den_ne c ε hε y)

/-- `∂_q Γ_ε` is `K₀^ε` (slice derivative). -/
lemma hasDerivAt_green_q (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => cylGreenReg c ε (t, y.2)) (cylKerReg c ε 0 y) y.1 := by
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (cylFreq c * t))
      (-Real.sin (cylFreq c * y.1) * (cylFreq c * 1)) y.1 :=
    ((hasDerivAt_id' y.1).const_mul (cylFreq c)).cos
  have hden : HasDerivAt
      (fun t : ℝ => Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * t) + ε)
      (cylFreq c * Real.sin (cylFreq c * y.1)) y.1 := by
    have := (hcos.const_sub (Real.cosh (cylFreq c * y.2))).add_const ε
    exact this.congr_deriv (by ring)
  have hg := (hden.log (den_ne c ε hε y)).const_mul (4 * Real.pi)⁻¹
  show HasDerivAt
    (fun t : ℝ => (4 * Real.pi)⁻¹ * Real.log
      (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * t) + ε)) _ y.1
  have hval : cylKerReg c ε 0 y = cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * y.1) /
      (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) := by
    simp [cylKerReg, cylNum, cylDen]
  rw [hval]
  exact hg.congr_deriv (by ring)

/-- `∂_η Γ_ε` is `K₁^ε` (slice derivative). -/
lemma hasDerivAt_green_eta (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => cylGreenReg c ε (y.1, t)) (cylKerReg c ε 1 y) y.2 := by
  have hcosh : HasDerivAt (fun t : ℝ => Real.cosh (cylFreq c * t))
      (Real.sinh (cylFreq c * y.2) * (cylFreq c * 1)) y.2 :=
    ((hasDerivAt_id' y.2).const_mul (cylFreq c)).cosh
  have hden : HasDerivAt
      (fun t : ℝ => Real.cosh (cylFreq c * t) - Real.cos (cylFreq c * y.1) + ε)
      (Real.sinh (cylFreq c * y.2) * (cylFreq c * 1)) y.2 :=
    (hcosh.sub_const (Real.cos (cylFreq c * y.1))).add_const ε
  have hne : Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε ≠ 0 :=
    den_ne c ε hε y
  have hg := (hden.log (by simpa using hne)).const_mul (4 * Real.pi)⁻¹
  show HasDerivAt
    (fun t : ℝ => (4 * Real.pi)⁻¹ * Real.log
      (Real.cosh (cylFreq c * t) - Real.cos (cylFreq c * y.1) + ε)) _ y.2
  have hval : cylKerReg c ε 1 y = cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) /
      (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) := by
    simp [cylKerReg, cylNum, cylDen]
  rw [hval]
  exact hg.congr_deriv (by ring)

/-- `∂_q K₀^ε` (quotient rule). -/
lemma hasDerivAt_K0_q (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => cylKerReg c ε 0 (t, y.2))
      ((cylFreq c / (4 * Real.pi) * (Real.cos (cylFreq c * y.1) * cylFreq c) *
          (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) -
        cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * y.1) *
          (Real.sin (cylFreq c * y.1) * cylFreq c)) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2) y.1 := by
  have hnum : HasDerivAt (fun t : ℝ => cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * t))
      (cylFreq c / (4 * Real.pi) * (Real.cos (cylFreq c * y.1) * (cylFreq c * 1))) y.1 :=
    (((hasDerivAt_id' y.1).const_mul (cylFreq c)).sin).const_mul _
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (cylFreq c * t))
      (-Real.sin (cylFreq c * y.1) * (cylFreq c * 1)) y.1 :=
    ((hasDerivAt_id' y.1).const_mul (cylFreq c)).cos
  have hden : HasDerivAt
      (fun t : ℝ => Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * t) + ε)
      (cylFreq c * Real.sin (cylFreq c * y.1)) y.1 := by
    have := (hcos.const_sub (Real.cosh (cylFreq c * y.2))).add_const ε
    exact this.congr_deriv (by ring)
  have hd := hnum.div hden (den_ne c ε hε y)
  exact hd.congr_deriv (by ring)

/-- `∂_η K₁^ε` (quotient rule). -/
lemma hasDerivAt_K1_eta (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => cylKerReg c ε 1 (y.1, t))
      ((cylFreq c / (4 * Real.pi) * (Real.cosh (cylFreq c * y.2) * cylFreq c) *
          (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) -
        cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) *
          (Real.sinh (cylFreq c * y.2) * cylFreq c)) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2) y.2 := by
  have hnum : HasDerivAt (fun t : ℝ => cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * t))
      (cylFreq c / (4 * Real.pi) * (Real.cosh (cylFreq c * y.2) * (cylFreq c * 1))) y.2 :=
    (((hasDerivAt_id' y.2).const_mul (cylFreq c)).sinh).const_mul _
  have hcosh : HasDerivAt (fun t : ℝ => Real.cosh (cylFreq c * t))
      (Real.sinh (cylFreq c * y.2) * (cylFreq c * 1)) y.2 :=
    ((hasDerivAt_id' y.2).const_mul (cylFreq c)).cosh
  have hden : HasDerivAt
      (fun t : ℝ => Real.cosh (cylFreq c * t) - Real.cos (cylFreq c * y.1) + ε)
      (Real.sinh (cylFreq c * y.2) * (cylFreq c * 1)) y.2 :=
    (hcosh.sub_const (Real.cos (cylFreq c * y.1))).add_const ε
  have hd := hnum.div hden (den_ne c ε hε y)
  exact hd.congr_deriv (by ring)

/-- Algebra of the Laplacian of `Γ_ε`: the two quotient-rule terms add up to `ρ_ε`. -/
lemma lap_alg (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) :
    (cylFreq c / (4 * Real.pi) * (Real.cos (cylFreq c * y.1) * cylFreq c) *
          (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) -
        cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * y.1) *
          (Real.sin (cylFreq c * y.1) * cylFreq c)) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2 +
    (cylFreq c / (4 * Real.pi) * (Real.cosh (cylFreq c * y.2) * cylFreq c) *
          (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) -
        cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) *
          (Real.sinh (cylFreq c * y.2) * cylFreq c)) /
        (Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2 =
      cylRho c ε y := by
  have hH : Real.cosh (cylFreq c * y.2) ^ 2 = Real.sinh (cylFreq c * y.2) ^ 2 + 1 :=
    Real.cosh_sq _
  have hSC : Real.sin (cylFreq c * y.1) ^ 2 + Real.cos (cylFreq c * y.1) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  unfold cylRho cylDen
  rw [← add_div, div_eq_div_iff (pow_ne_zero 2 (den_ne c ε hε y))
    (pow_ne_zero 2 (den_ne c ε hε y))]
  linear_combination
    ((Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2 * cylFreq c ^ 2 /
      (4 * Real.pi)) * hH -
    ((Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) + ε) ^ 2 * cylFreq c ^ 2 /
      (4 * Real.pi)) * hSC

/-- **Calculus of `Γ_ε`** (source 1676). -/
theorem regKerCalc : RegKerCalc := by
  intro c ε hc hε
  have hG := contDiff_cylGreenReg c ε hε
  have hfun0 : pd2 0 (cylGreenReg c ε) = cylKerReg c ε 0 := by
    funext y
    exact pd2_zero_eq_of_hasDerivAt _ y _ (hG.differentiable (by simp) y)
      (hasDerivAt_green_q c ε hε y)
  have hfun1 : pd2 1 (cylGreenReg c ε) = cylKerReg c ε 1 := by
    funext y
    exact pd2_one_eq_of_hasDerivAt _ y _ (hG.differentiable (by simp) y)
      (hasDerivAt_green_eta c ε hε y)
  refine ⟨hG, ?_, ?_, ?_⟩
  · intro y
    have hper : cylFreq c * (y.1 + c) = cylFreq c * y.1 + 2 * Real.pi := by
      unfold cylFreq
      field_simp
    simp only [cylGreenReg, cylDen]
    rw [hper, Real.cos_add_two_pi]
  · intro i y
    fin_cases i
    · exact congrFun hfun0 y
    · exact congrFun hfun1 y
  · intro y
    unfold lap2
    rw [hfun0, hfun1]
    rw [pd2_zero_eq_of_hasDerivAt (cylKerReg c ε 0) y _
      ((contDiff_cylKerReg_zero c ε hε).differentiable (by simp) y)
      (hasDerivAt_K0_q c ε hε y)]
    rw [pd2_one_eq_of_hasDerivAt (cylKerReg c ε 1) y _
      ((contDiff_cylKerReg_one c ε hε).differentiable (by simp) y)
      (hasDerivAt_K1_eta c ε hε y)]
    exact lap_alg c ε hε y

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
