import UnforcedLeray.Lib.Sobolev.WeakDeriv
import NonUniqueEuler.Defs.Infra.Sobolev
import Mathlib.Analysis.Complex.Basic

/-!
# Bridge to the vendored NonUniqueEuler weak derivatives (INF11 target S3, second part)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S3: `nue_hasWeakDerivOn_iff`) and §3.3 (the
NonUniqueEuler reference is complex valued, with complex tests). The vendored predicate is
`NonUniqueEuler.Sob.HasWeakDerivOn` (`lean/NonUniqueEuler/Defs/Infra/Sobolev.lean:76`):
`∫ f · ∂_{vs} φ = (-1)^{|vs|} ∫ g · φ` for complex tests `φ` supported in `V`, with no
integrability clause. For locally integrable `f, g` and `V = univ` it is the same as
`HasWeakDeriv (wholeSpace n) vs f g` (real tests, integrable pairings): a complex test splits
into its real and imaginary parts, and a real test is a complex one.

## Main declarations
* `nue_iterDirDeriv_ofReal`, `iterDirDeriv_re`, `iterDirDeriv_im`: the two iterated
  derivatives commute with `ℝ → ℂ` and with `re`, `im`;
* `nue_hasWeakDerivOn_iff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nue_contDiff_iterDirDeriv {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List E) :
    ContDiff ℝ ∞ (NonUniqueEuler.Sob.iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa [NonUniqueEuler.Sob.iterDirDeriv] using h
  | cons v vs ih =>
    exact (ContDiff.fderiv_right (m := ∞) ih (by simp)).clm_apply contDiff_const

/-- `∂_{vs} (φ : ℂ) = (∂_{vs} φ : ℂ)` for a smooth real `φ`. -/
theorem nue_iterDirDeriv_ofReal {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (vs : List E) :
    NonUniqueEuler.Sob.iterDirDeriv vs (fun x => (φ x : ℂ)) =
      fun x => (iterDirDeriv vs φ x : ℂ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    show fderiv ℝ (NonUniqueEuler.Sob.iterDirDeriv vs (fun x => (φ x : ℂ))) x v =
      ((fderiv ℝ (iterDirDeriv vs φ) x v : ℝ) : ℂ)
    rw [ih]
    have hd : DifferentiableAt ℝ (iterDirDeriv vs φ) x :=
      (contDiff_iterDirDeriv hφ vs).differentiable (by simp) x
    have hD : HasFDerivAt (fun y => ((iterDirDeriv vs φ y : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (iterDirDeriv vs φ) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
    rw [hD.fderiv]
    rfl

/-- `∂_{vs} (re φ) = re (∂_{vs} φ)` for a smooth complex `φ`. -/
theorem iterDirDeriv_re {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (vs : List E) :
    iterDirDeriv vs (fun x => (φ x).re) =
      fun x => (NonUniqueEuler.Sob.iterDirDeriv vs φ x).re := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    show fderiv ℝ (iterDirDeriv vs (fun x => (φ x).re)) x v =
      (fderiv ℝ (NonUniqueEuler.Sob.iterDirDeriv vs φ) x v).re
    rw [ih]
    have hd : DifferentiableAt ℝ (NonUniqueEuler.Sob.iterDirDeriv vs φ) x :=
      (nue_contDiff_iterDirDeriv hφ vs).differentiable (by simp) x
    have hD : HasFDerivAt (fun y => (NonUniqueEuler.Sob.iterDirDeriv vs φ y).re)
        (Complex.reCLM.comp (fderiv ℝ (NonUniqueEuler.Sob.iterDirDeriv vs φ) x)) x :=
      Complex.reCLM.hasFDerivAt.comp x hd.hasFDerivAt
    rw [hD.fderiv]
    rfl

/-- `∂_{vs} (im φ) = im (∂_{vs} φ)` for a smooth complex `φ`. -/
theorem iterDirDeriv_im {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (vs : List E) :
    iterDirDeriv vs (fun x => (φ x).im) =
      fun x => (NonUniqueEuler.Sob.iterDirDeriv vs φ x).im := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    show fderiv ℝ (iterDirDeriv vs (fun x => (φ x).im)) x v =
      (fderiv ℝ (NonUniqueEuler.Sob.iterDirDeriv vs φ) x v).im
    rw [ih]
    have hd : DifferentiableAt ℝ (NonUniqueEuler.Sob.iterDirDeriv vs φ) x :=
      (nue_contDiff_iterDirDeriv hφ vs).differentiable (by simp) x
    have hD : HasFDerivAt (fun y => (NonUniqueEuler.Sob.iterDirDeriv vs φ y).im)
        (Complex.imCLM.comp (fderiv ℝ (NonUniqueEuler.Sob.iterDirDeriv vs φ) x)) x :=
      Complex.imCLM.hasFDerivAt.comp x hd.hasFDerivAt
    rw [hD.fderiv]
    rfl

end Calculus

/-- **Bridge to NonUniqueEuler** (S3): for locally integrable `f, g : ℝⁿ → ℂ`, the vendored
`HasWeakDerivOn univ vs f g` (complex tests) is `HasWeakDeriv (wholeSpace n) vs f g` (real
tests). -/
theorem nue_hasWeakDerivOn_iff {n : ℕ} {vs : List (Eucl n)} {f g : Eucl n → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    NonUniqueEuler.Sob.HasWeakDerivOn univ vs f g ↔ HasWeakDeriv (wholeSpace n) vs f g := by
  have hint : ∀ ψ : Eucl n → ℝ, (wholeSpace n).Adm ψ → ∀ u : Eucl n → ℂ,
      LocallyIntegrable u volume → Integrable (fun x => ψ x • u x) volume :=
    fun ψ hψ u hu => hu.integrable_smul_left_of_hasCompactSupport hψ.1.continuous hψ.2
  have hW : HasWeakDeriv (wholeSpace n) vs f g ↔ ∀ φ, (wholeSpace n).Adm φ →
      ∫ x, (iterDirDeriv vs φ x : ℂ) * f x = ((-1 : ℝ) ^ vs.length : ℝ) *
        ∫ x, (φ x : ℂ) * g x := by
    constructor
    · intro h φ hφ
      have := h.identity φ hφ
      simpa only [wholeSpace_μ, Complex.real_smul] using this
    · intro h
      refine ⟨fun φ hφ => hint _ ((wholeSpace n).adm_iterDirDeriv hφ vs) f hf,
        fun φ hφ => hint φ hφ g hg, fun φ hφ => ?_⟩
      simpa only [wholeSpace_μ, Complex.real_smul] using h φ hφ
  rw [hW]
  have i1 : ∀ ψ : Eucl n → ℝ, (wholeSpace n).Adm ψ → ∀ u : Eucl n → ℂ,
      LocallyIntegrable u volume → Integrable (fun x => (ψ x : ℂ) * u x) volume :=
    fun ψ hψ u hu => by simpa only [Complex.real_smul] using hint ψ hψ u hu
  constructor
  · intro h φ hφ
    have hT : NonUniqueEuler.Sob.IsTestFn univ (fun x => (φ x : ℂ)) :=
      ⟨Complex.ofRealCLM.contDiff.comp hφ.1, hφ.2.comp_left Complex.ofReal_zero,
        subset_univ _⟩
    have := h _ hT
    rw [nue_iterDirDeriv_ofReal hφ.1] at this
    calc ∫ x, (iterDirDeriv vs φ x : ℂ) * f x
        = ∫ x, f x * (iterDirDeriv vs φ x : ℂ) := by congr 1 with x; ring
      _ = (-1 : ℂ) ^ vs.length * ∫ x, g x * (φ x : ℂ) := this
      _ = ((-1 : ℝ) ^ vs.length : ℝ) * ∫ x, (φ x : ℂ) * g x := by
          push_cast
          congr 2 with x
          ring
  · intro h φ hφ
    set a : Eucl n → ℝ := fun x => (φ x).re with ha_def
    set b : Eucl n → ℝ := fun x => (φ x).im with hb_def
    have haA : (wholeSpace n).Adm a :=
      ⟨Complex.reCLM.contDiff.comp hφ.smooth, hφ.compact.comp_left Complex.zero_re⟩
    have hbA : (wholeSpace n).Adm b :=
      ⟨Complex.imCLM.contDiff.comp hφ.smooth, hφ.compact.comp_left Complex.zero_im⟩
    have ha := h a haA
    have hb := h b hbA
    have hφx : ∀ x, φ x = (a x : ℂ) + (b x : ℂ) * Complex.I :=
      fun x => (Complex.re_add_im (φ x)).symm
    have hre := iterDirDeriv_re hφ.smooth vs
    have him := iterDirDeriv_im hφ.smooth vs
    have hdx : ∀ x, NonUniqueEuler.Sob.iterDirDeriv vs φ x =
        (iterDirDeriv vs a x : ℂ) + (iterDirDeriv vs b x : ℂ) * Complex.I := by
      intro x
      rw [hre, him]
      exact (Complex.re_add_im _).symm
    have j1 := i1 _ ((wholeSpace n).adm_iterDirDeriv haA vs) f hf
    have j2 := i1 _ ((wholeSpace n).adm_iterDirDeriv hbA vs) f hf
    have j3 := i1 a haA g hg
    have j4 := i1 b hbA g hg
    have hg' : ∫ x, g x * φ x =
        (∫ x, (a x : ℂ) * g x) + (∫ x, (b x : ℂ) * g x) * Complex.I := by
      rw [← integral_mul_const, ← integral_add j3 (j4.mul_const _)]
      congr 1 with x
      rw [hφx]
      ring
    calc ∫ x, f x * NonUniqueEuler.Sob.iterDirDeriv vs φ x
        = ∫ x, ((iterDirDeriv vs a x : ℂ) * f x +
            (iterDirDeriv vs b x : ℂ) * f x * Complex.I) := by
          congr 1 with x
          rw [hdx]
          ring
      _ = (∫ x, (iterDirDeriv vs a x : ℂ) * f x) +
            (∫ x, (iterDirDeriv vs b x : ℂ) * f x) * Complex.I := by
          rw [integral_add j1 (j2.mul_const _), integral_mul_const]
      _ = (((-1 : ℝ) ^ vs.length : ℝ) : ℂ) * (∫ x, (a x : ℂ) * g x) +
            ((((-1 : ℝ) ^ vs.length : ℝ) : ℂ) * ∫ x, (b x : ℂ) * g x) * Complex.I := by
          rw [ha, hb]
      _ = (-1 : ℂ) ^ vs.length * ∫ x, g x * φ x := by
          rw [hg']
          push_cast
          ring

end UnforcedLeray.Sob
