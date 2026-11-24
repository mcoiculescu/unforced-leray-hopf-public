import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1_3
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIb.GDiffHelp

/-- The point `-(y₀ + i y₁)` lies in the slit plane when `y` is off the axis and off the half-line. -/
lemma neg_mk_mem_slitPlane {y : UnforcedLeray.Space} (hax : y ∉ UnforcedLeray.Axi.axis)
    (hy : ¬ (0 < y 0 ∧ y 1 = 0)) : (-(⟨y 0, y 1⟩ : ℂ)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  show 0 < -(y 0) ∨ -(y 1) ≠ 0
  by_cases h1 : y 1 = 0
  · left
    have h0 : y 0 < 0 := by
      rcases lt_trichotomy (y 0) 0 with h | h | h
      · exact h
      · exact absurd (show y ∈ UnforcedLeray.Axi.axis from ⟨h, h1⟩) hax
      · exact absurd ⟨h, h1⟩ hy
    linarith
  · right
    exact neg_ne_zero.mpr h1

lemma neg_mk_differentiableAt (y : UnforcedLeray.Space) :
    DifferentiableAt ℝ (fun z : UnforcedLeray.Space => -(⟨z 0, z 1⟩ : ℂ)) y := by
  have hc : ∀ z : UnforcedLeray.Space,
      (⟨z 0, z 1⟩ : ℂ) = ((z 0 : ℝ) : ℂ) + ((z 1 : ℝ) : ℂ) * Complex.I :=
    fun z => Complex.mk_eq_add_mul_I _ _
  simp only [hc]
  fun_prop

lemma psiAz_differentiableAt {y : UnforcedLeray.Space} (hax : y ∉ UnforcedLeray.Axi.axis)
    (hy : ¬ (0 < y 0 ∧ y 1 = 0)) :
    DifferentiableAt ℝ (fun z : UnforcedLeray.Space => UnforcedLeray.Short.IIb.psiAz z) y := by
  have hs := neg_mk_mem_slitPlane hax hy
  have hL : DifferentiableAt ℝ (fun w : ℂ => (Complex.log w).im)
      (-(⟨y 0, y 1⟩ : ℂ)) :=
    (Complex.imCLM.differentiableAt.comp (-(⟨y 0, y 1⟩ : ℂ))
      ((Complex.differentiableAt_log hs).restrictScalars ℝ))
  have hfun : (fun z : UnforcedLeray.Space => UnforcedLeray.Short.IIb.psiAz z)
      = fun z : UnforcedLeray.Space =>
          Real.pi + (Complex.log (-(⟨z 0, z 1⟩ : ℂ))).im := by
    funext z
    simp [UnforcedLeray.Short.IIb.psiAz, Complex.log_im]
  rw [hfun]
  exact (hL.comp y (neg_mk_differentiableAt y)).const_add Real.pi

end UnforcedLeray.Short.IIb.GDiffHelp

open UnforcedLeray.Short.IIb.GDiffHelp in
theorem psi_g_diff : UnforcedLeray.Short.IIb.PsiGDiff := by
  unfold UnforcedLeray.Short.IIb.PsiGDiff
  intro R hR
  have hR0 : R ≠ 0 := hR.ne'
  unfold DifferentiableOn
  intro x hx
  have hx' : x.2 ∉ UnforcedLeray.Axi.axis ∧ ¬ (0 < x.2 0 ∧ x.2 1 = 0) := hx
  obtain ⟨hax, hy⟩ := hx'
  apply DifferentiableAt.differentiableWithinAt
  have hage : UnforcedLeray.Axi.age R x.2 ≠ 0 := by
    unfold UnforcedLeray.Axi.age
    exact div_ne_zero (pow_ne_zero 2 hR0) (pow_ne_zero 2 (UnforcedLeray.Axi.ϱ_ne_zero hax))
  have hA : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.age R x.2) x :=
    (UnforcedLeray.Axi.hasFDerivAt_age R hax).differentiableAt.comp x differentiableAt_snd
  have hP : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.phase R x.1 x.2) x := by
    unfold UnforcedLeray.Axi.phase
    have hl : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space =>
        Real.log (UnforcedLeray.Axi.age R x.2)) x := hA.log hage
    have h1 : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => R * x.1) x :=
      differentiableAt_fst.const_mul R
    have h2 : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => (1/2:ℝ) * (R * x.1)) x :=
      h1.const_mul (1/2:ℝ)
    have key : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space =>
        (1/2:ℝ) * (R * x.1) - (R / 2) * Real.log (UnforcedLeray.Axi.age R x.2)) x :=
      h2.sub (hl.const_mul (R / 2))
    convert key using 1
    funext z
    ring
  have hT : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.trans R x.2) x :=
    (UnforcedLeray.Axi.hasFDerivAt_trans R hax).differentiableAt.comp x differentiableAt_snd
  have hchart : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.chart R x.1 x.2) x := by
    unfold UnforcedLeray.Axi.chart
    exact hA.prodMk (hP.prodMk hT)
  have haz : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Short.IIb.psiAz x.2) x :=
    (psiAz_differentiableAt hax hy).comp x differentiableAt_snd
  unfold UnforcedLeray.Short.IIb.psiG
  exact hchart.prodMk haz
