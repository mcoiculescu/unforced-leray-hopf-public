import UnforcedLeray.Short.PartI.Sub.C09.PlanarEllipticH2.Lap

/-!
# Complex test functions for weak derivatives on `Eucl 2` (helper for `PartI:PlanarEllipticH2`)

`HasWeakDeriv (wholeSpace 2) vs f g` only tests against real `C_c^∞` functions. Here the identity is
extended to complex-valued smooth compactly supported tests `ψ`, by splitting `ψ` into its real and
imaginary parts (`iterD_post_clm` applied to `reCLM` and `imCLM`).

* `hasWeakDeriv_complex_test`: `∫ (∂_{vs} ψ) f = (-1)^{|vs|} ∫ ψ g` for complex `ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

theorem hasWeakDeriv_complex_test {vs : List (UnforcedLeray.Sob.Eucl 2)}
    {f g : UnforcedLeray.Sob.Eucl 2 → ℂ}
    (h : UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.wholeSpace 2) vs f g)
    {ψ : UnforcedLeray.Sob.Eucl 2 → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, UnforcedLeray.PlanarBS.Sob.iterDirDeriv vs ψ x * f x =
      (-1 : ℂ) ^ vs.length * ∫ x, ψ x * g x := by
  have hw : ∀ w : ℂ, w = ((Complex.reCLM w : ℝ) : ℂ) + Complex.I * ((Complex.imCLM w : ℝ) : ℂ) := by
    intro w
    apply Complex.ext <;> simp
  have ha : ContDiff ℝ ∞ (fun x => Complex.reCLM (ψ x)) := Complex.reCLM.contDiff.comp hψ
  have hb : ContDiff ℝ ∞ (fun x => Complex.imCLM (ψ x)) := Complex.imCLM.contDiff.comp hψ
  have hac : HasCompactSupport (fun x => Complex.reCLM (ψ x)) :=
    hψc.comp_left (g := Complex.reCLM) (by simp)
  have hbc : HasCompactSupport (fun x => Complex.imCLM (ψ x)) :=
    hψc.comp_left (g := Complex.imCLM) (by simp)
  have adma : (UnforcedLeray.Sob.wholeSpace 2).Adm (fun x => Complex.reCLM (ψ x)) :=
    (UnforcedLeray.Sob.wholeSpace_adm 2 _).mpr ⟨ha, hac⟩
  have admb : (UnforcedLeray.Sob.wholeSpace 2).Adm (fun x => Complex.imCLM (ψ x)) :=
    (UnforcedLeray.Sob.wholeSpace_adm 2 _).mpr ⟨hb, hbc⟩
  have ea : ∀ x, UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.reCLM (ψ x)) x =
      Complex.reCLM (UnforcedLeray.PlanarBS.Sob.iterDirDeriv vs ψ x) := fun x =>
    congrFun (iterD_post_clm Complex.reCLM hψ vs) x
  have eb : ∀ x, UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.imCLM (ψ x)) x =
      Complex.imCLM (UnforcedLeray.PlanarBS.Sob.iterDirDeriv vs ψ x) := fun x =>
    congrFun (iterD_post_clm Complex.imCLM hψ vs) x
  -- pointwise splitting of the derivative of `ψ`
  have hpt : ∀ x, UnforcedLeray.PlanarBS.Sob.iterDirDeriv vs ψ x * f x =
      ((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.reCLM (ψ x)) x : ℝ) : ℂ) * f x +
        Complex.I * (((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.imCLM (ψ x)) x : ℝ) : ℂ) *
          f x) := by
    intro x
    rw [ea x, eb x]
    conv_lhs => rw [hw (UnforcedLeray.PlanarBS.Sob.iterDirDeriv vs ψ x)]
    ring
  have hpg : ∀ x, ψ x * g x = ((Complex.reCLM (ψ x) : ℝ) : ℂ) * g x +
      Complex.I * (((Complex.imCLM (ψ x) : ℝ) : ℂ) * g x) := by
    intro x
    conv_lhs => rw [hw (ψ x)]
    ring
  -- integrability of the four pieces
  have iA := h.int_left _ adma
  have iB := h.int_left _ admb
  have gA := h.int_right _ adma
  have gB := h.int_right _ admb
  simp only [UnforcedLeray.Sob.wholeSpace_μ, Complex.real_smul] at iA iB gA gB
  have hI1 := h.identity _ adma
  have hI2 := h.identity _ admb
  simp only [UnforcedLeray.Sob.wholeSpace_μ, Complex.real_smul] at hI1 hI2
  have e1 : ∫ x, UnforcedLeray.PlanarBS.Sob.iterDirDeriv vs ψ x * f x =
      ∫ x, (((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.reCLM (ψ x)) x : ℝ) : ℂ) * f x) +
        Complex.I * (((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.imCLM (ψ x)) x : ℝ) : ℂ) *
          f x) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have e2 : ∫ x, ψ x * g x = ∫ x, ((Complex.reCLM (ψ x) : ℝ) : ℂ) * g x +
      Complex.I * (((Complex.imCLM (ψ x) : ℝ) : ℂ) * g x) :=
    integral_congr_ae (Filter.Eventually.of_forall hpg)
  have hc : (((-1 : ℝ) ^ vs.length : ℝ) : ℂ) = (-1 : ℂ) ^ vs.length := by push_cast; ring
  have s1 : ∫ x, (((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.reCLM (ψ x)) x : ℝ) : ℂ) *
        f x + Complex.I * (((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.imCLM (ψ x)) x : ℝ) : ℂ) *
          f x)) =
      (∫ x, ((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.reCLM (ψ x)) x : ℝ) : ℂ) * f x) +
        Complex.I * ∫ x, (((UnforcedLeray.Sob.iterDirDeriv vs (fun x => Complex.imCLM (ψ x)) x : ℝ) : ℂ) *
          f x) := by
    rw [integral_add iA (iB.const_mul Complex.I), integral_const_mul]
  have s2 : ∫ x, (((Complex.reCLM (ψ x) : ℝ) : ℂ) * g x + Complex.I * (((Complex.imCLM (ψ x) : ℝ) : ℂ) * g x)) =
      (∫ x, ((Complex.reCLM (ψ x) : ℝ) : ℂ) * g x) + Complex.I * ∫ x, (((Complex.imCLM (ψ x) : ℝ) : ℂ) * g x) := by
    rw [integral_add gA (gB.const_mul Complex.I), integral_const_mul]
  have hI1' := hI1
  have hI2' := hI2
  rw [hc] at hI1' hI2'
  rw [e1, s1, e2, s2]
  linear_combination hI1' + Complex.I * hI2'

end UnforcedLeray.Short.PartI
