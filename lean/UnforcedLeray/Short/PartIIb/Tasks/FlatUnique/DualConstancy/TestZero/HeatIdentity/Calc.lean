import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2

/-!
# Helper for `PartII-b:T11/2/2/3` (`DualHeatIdentity`): calculus on the open slab
`W = (0,s) × ℝ²`, product rule with a `σ`-only factor, mixed partials, `ℝ → ℂ` transfer.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

section general

variable {W : Set Coord}

theorem cpd_contDiffOn' (hW : IsOpen W) {f : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f W) (j : Fin 3) :
    ContDiffOn ℝ ∞ (cpd j f) W := by
  show ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (cdir j)) W
  exact (hf.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const

theorem cpdC_contDiffOn' (hW : IsOpen W) {F : Coord → ℂ} (hF : ContDiffOn ℝ ∞ F W) (j : Fin 3) :
    ContDiffOn ℝ ∞ (cpdC j F) W := by
  show ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x (cdir j)) W
  exact (hF.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const

theorem cpd_congr_on (hW : IsOpen W) {f g : Coord → ℝ} (h : ∀ y ∈ W, f y = g y) (j : Fin 3) :
    ∀ y ∈ W, cpd j f y = cpd j g y := by
  intro y hy
  have : f =ᶠ[𝓝 y] g := by
    filter_upwards [hW.mem_nhds hy] with z hz using h z hz
  simp [cpd, this.fderiv_eq]

theorem cpdC_congr_on (hW : IsOpen W) {f g : Coord → ℂ} (h : ∀ y ∈ W, f y = g y) (j : Fin 3) :
    ∀ y ∈ W, cpdC j f y = cpdC j g y := by
  intro y hy
  have : f =ᶠ[𝓝 y] g := by
    filter_upwards [hW.mem_nhds hy] with z hz using h z hz
  simp [cpdC, this.fderiv_eq]

theorem cpd_swap (hW : IsOpen W) {f : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f W) (j k : Fin 3) :
    ∀ y ∈ W, cpd j (cpd k f) y = cpd k (cpd j f) y := by
  intro y hy
  have hfy : ContDiffAt ℝ ∞ f y := hf.contDiffAt (hW.mem_nhds hy)
  have hsym := hfy.isSymmSndFDerivAt (by simp [minSmoothness])
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hfy.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have key : ∀ j k, cpd j (cpd k f) y = fderiv ℝ (fderiv ℝ f) y (cdir j) (cdir k) := by
    intro j k
    show fderiv ℝ (fun z => fderiv ℝ f z (cdir k)) y (cdir j) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]; exact hsym _ _

theorem cpdC_ofReal {f : Coord → ℝ} {y : Coord} (hf : DifferentiableAt ℝ f y) (j : Fin 3) :
    cpdC j (fun z => (f z : ℂ)) y = (cpd j f y : ℂ) := by
  have h : HasFDerivAt (fun z => (f z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hf.hasFDerivAt
  simp [cpdC, cpd, h.fderiv]

theorem cpdC_ofReal_on (hW : IsOpen W) {F : Coord → ℂ} {f : Coord → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hF : ∀ y ∈ W, F y = (f y : ℂ)) (j : Fin 3) :
    ∀ y ∈ W, cpdC j F y = (cpd j f y : ℂ) := by
  intro y hy
  rw [cpdC_congr_on hW hF j y hy]
  exact cpdC_ofReal ((hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num)) j

theorem cpdC_mul_a (hW : IsOpen W) (a : ℝ → ℂ) (ha : ∀ y ∈ W, DifferentiableAt ℝ a y.1)
    {F F0 : Coord → ℂ} (hF : ∀ y ∈ W, F y = a y.1 * F0 y) (hF0 : ContDiffOn ℝ ∞ F0 W)
    (j : Fin 3) : ∀ y ∈ W, cpdC j F y =
      a y.1 * cpdC j F0 y + F0 y * (((cdir j).1 : ℝ) • deriv a y.1) := by
  intro y hy
  have hF0d : DifferentiableAt ℝ F0 y :=
    (hF0.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num)
  have had : HasDerivAt a (deriv a y.1) y.1 := (ha y hy).hasDerivAt
  have hA := had.hasFDerivAt.comp y (hasFDerivAt_fst (𝕜 := ℝ) (p := y))
  have hP := hA.mul hF0d.hasFDerivAt
  have hev : F =ᶠ[𝓝 y] fun z => a z.1 * F0 z := by
    filter_upwards [hW.mem_nhds hy] with z hz using hF z hz
  rw [cpdC, hev.fderiv_eq, show fderiv ℝ (fun z : Coord => a z.1 * F0 z) y = _ from hP.fderiv]
  simp [cpdC, mul_comm]

theorem cpdC_mul_a_qeta (hW : IsOpen W) (a : ℝ → ℂ) (ha : ∀ y ∈ W, DifferentiableAt ℝ a y.1)
    {F F0 : Coord → ℂ} (hF : ∀ y ∈ W, F y = a y.1 * F0 y) (hF0 : ContDiffOn ℝ ∞ F0 W)
    (j : Fin 3) (hj : (cdir j).1 = 0) : ∀ y ∈ W, cpdC j F y = a y.1 * cpdC j F0 y := by
  intro y hy
  rw [cpdC_mul_a hW a ha hF hF0 j y hy, hj]; simp

theorem cpdC_mul_a_s (hW : IsOpen W) (a : ℝ → ℂ) (ha : ∀ y ∈ W, DifferentiableAt ℝ a y.1)
    {F F0 : Coord → ℂ} (hF : ∀ y ∈ W, F y = a y.1 * F0 y) (hF0 : ContDiffOn ℝ ∞ F0 W) :
    ∀ y ∈ W, cpdC 0 F y = a y.1 * cpdC 0 F0 y + F0 y * deriv a y.1 := by
  intro y hy
  rw [cpdC_mul_a hW a ha hF hF0 0 y hy]
  simp [cdir]

end general

theorem cpdC_neg' (F : Coord → ℂ) (j : Fin 3) (x : Coord) :
    cpdC j (fun z => -F z) x = -cpdC j F x := by
  simp [cpdC, fderiv_neg]

/-- smoothness of `u ↦ u^(μ-1)` at positive points. -/
theorem contDiffAt_cpow_aux2 (μ : ℂ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun u : ℝ => (u : ℂ) ^ (μ - 1)) t := by
  have hz : (t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using ht
  have hlog : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.log (u : ℂ)) t :=
    ((Complex.contDiffAt_log hz).restrict_scalars ℝ).comp t
      (Complex.ofRealCLM.contDiff.contDiffAt)
  have hmul : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.log (u : ℂ) * (μ - 1)) t :=
    hlog.mul contDiffAt_const
  have hexp : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.exp (Complex.log (u : ℂ) * (μ - 1))) t := by
    first
    | exact hmul.cexp
    | exact ((Complex.contDiff_exp).contDiffAt.restrict_scalars ℝ).comp t hmul
  apply hexp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
  exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt hu)) _

theorem hasDerivAt_dualA (μ : ℂ) (χ : ℝ → ℝ) (t : ℝ) (ht : 0 < t) (hχ : DifferentiableAt ℝ χ t) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (χ u : ℂ))
      ((μ - 1) * (t : ℂ) ^ (μ - 1 - 1) * (χ t : ℂ) +
        (t : ℂ) ^ (μ - 1) * ((deriv χ t : ℝ) : ℂ)) t := by
  have hz : (t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using ht
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (μ - 1)) ((μ - 1) * (t : ℂ) ^ (μ - 1 - 1)) t :=
    (Complex.hasStrictDerivAt_cpow_const (c := μ - 1) hz).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun u : ℝ => (χ u : ℂ)) ((deriv χ t : ℝ) : ℂ) t :=
    hχ.hasDerivAt.ofReal_comp
  exact h1.mul h2

theorem cpow_alg (μ : ℂ) (χ : ℝ → ℝ) (t : ℝ) (ht : 0 < t) (hχ : DifferentiableAt ℝ χ t) :
    (μ - 1) * ((t : ℂ) ^ (μ - 1) * (χ t : ℂ)) -
      (t : ℂ) * deriv (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (χ u : ℂ)) t =
    -((t : ℂ) ^ μ * ((deriv χ t : ℝ) : ℂ)) := by
  rw [(hasDerivAt_dualA μ χ t ht hχ).deriv]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : (t : ℂ) * (t : ℂ) ^ (μ - 1 - 1) = (t : ℂ) ^ (μ - 1) := by
    conv_rhs => rw [show μ - 1 = (μ - 1 - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]; ring
  have e2 : (t : ℂ) ^ μ = (t : ℂ) * (t : ℂ) ^ (μ - 1) := by
    conv_lhs => rw [show μ = (μ - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]; ring
  rw [e2]
  linear_combination (-((μ - 1) * (χ t : ℂ))) * e1

end UnforcedLeray.Short.IIb
