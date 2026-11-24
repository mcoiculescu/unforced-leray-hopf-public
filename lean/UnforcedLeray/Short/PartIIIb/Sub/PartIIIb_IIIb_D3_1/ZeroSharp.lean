import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.BmatSharp
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatBound
import UnforcedLeray.Lib.SpecialFunctions.EulerGamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The Laplace row bound uniform in `ν` (source 4863-4864)

`|a₀(B_{μ,ν}[A])| ≤ ‖ℓ₊‖ (1+μ) C₀ Γ(μ+5/2)(γ-a_s)^{-μ-5/2} ‖A‖_𝒜` for `a_s < γ = Re λ`, because
the Laplace integrand is bounded by `C t^{μ+3/2} e^{-(γ-a_s)t}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `Γ(μ+5/2)(γ-a_s)^{-(μ+5/2)}`. -/
def gamFac (μ r : ℝ) : ℝ := (1 / r) ^ (μ + 5 / 2) * Real.Gamma (μ + 5 / 2)

theorem aZero_sharp {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (as ν μ : ℝ) (lam ell : ℂ) (A : ℝ → Mat3), 0 < ν → 0 ≤ μ →
      IsAffElem as A → as < lam.re →
      ‖aZero lam ell (μ : ℂ) (Bmat ν μ χ A)‖ ≤
        ‖ell‖ * ((1 + μ) * C0 * gamFac μ (lam.re - as)) * affNorm as A := by
  obtain ⟨C0, hC0, hpt⟩ := bmat_pointwise hχ
  refine ⟨C0, hC0, ?_⟩
  intro as ν μ lam ell A hν hμ hA hlam
  have hr : 0 < lam.re - as := by linarith
  set r := lam.re - as with hrdef
  set Kc : ℝ := 2 * ((1 + μ) * C0 * affNorm as A) with hKc
  have hn := affNorm_nonneg as A hA
  have hKc0 : 0 ≤ Kc := by
    have : 0 ≤ 1 + μ := by linarith
    positivity
  set g : ℝ → ℝ := fun t => Kc * (t ^ (μ + 3 / 2) * Real.exp (-(r * t))) with hg
  have hgi : IntegrableOn g (Ioi 0) :=
    Integrable.const_mul (UnforcedLeray.Special.integrableOn_rpow_mul_exp_neg_mul_Ioi
      (s := μ + 3 / 2) (b := r) (by linarith) hr) Kc
  have hbd : ∀ t ∈ Ioi (0 : ℝ), ‖azInt lam μ (Bmat ν μ χ A) t‖ ≤ g t := by
    intro t ht
    have ht : 0 < t := ht
    have hg0 : 0 ≤ g t := mul_nonneg hKc0
      (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    by_cases htT : t ≤ (11 / 10 : ℝ) / ν
    · have hb := hpt as ν μ A hν hμ hA t ht htT
      have hP : ‖(t : ℂ) ^ (μ : ℂ)‖ = t ^ μ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.ofReal_re]
      have hE : ‖Complex.exp (-lam * (t : ℂ))‖ = Real.exp (-(lam.re * t)) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      have hQ := norm_azQ_le (Bmat ν μ χ A t)
      have hsplit : ‖azInt lam μ (Bmat ν μ χ A) t‖ = ‖(t : ℂ) ^ (μ : ℂ)‖ *
          ‖Complex.exp (-lam * (t : ℂ))‖ * ‖((Bd (Bmat ν μ χ A t) : ℝ) : ℂ) -
            Complex.I * ((Be (Bmat ν μ χ A t) : ℝ) : ℂ)‖ := by
        unfold azInt
        rw [norm_mul, norm_mul]
      rw [hsplit, hP, hE]
      have hpe : t ^ μ * Real.exp (-(lam.re * t)) ≥ 0 :=
        mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
      calc t ^ μ * Real.exp (-(lam.re * t)) * ‖((Bd (Bmat ν μ χ A t) : ℝ) : ℂ) -
              Complex.I * ((Be (Bmat ν μ χ A t) : ℝ) : ℂ)‖
          ≤ t ^ μ * Real.exp (-(lam.re * t)) * (2 * frob (Bmat ν μ χ A t)) :=
            mul_le_mul_of_nonneg_left hQ hpe
        _ ≤ t ^ μ * Real.exp (-(lam.re * t)) *
              (2 * ((1 + μ) * C0 * (t ^ (3 / 2 : ℝ) * Real.exp (as * t)) * affNorm as A)) :=
            mul_le_mul_of_nonneg_left (by linarith) hpe
        _ = g t := by
            rw [hg, hKc]
            have h1 : t ^ (μ + 3 / 2) = t ^ μ * t ^ (3 / 2 : ℝ) := Real.rpow_add ht _ _
            have h2 : Real.exp (-(r * t)) = Real.exp (-(lam.re * t)) * Real.exp (as * t) := by
              rw [← Real.exp_add, hrdef]; congr 1; ring
            simp only [h1, h2]
            ring
    · rw [azInt_zero_of_Bmat_zero lam μ _ t
        (azBmat_zero hχ μ hν A t (lt_of_not_ge htT))]
      simpa using hg0
  have hint := norm_integral_le_of_norm_le hgi
    (ae_restrict_of_forall_mem measurableSet_Ioi hbd)
  have hGam : ∫ t in Ioi (0 : ℝ), g t = Kc * gamFac μ r := by
    rw [hg, integral_const_mul]
    congr 1
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := μ + 5 / 2) (r := r) (by linarith) hr
    rw [show μ + 5 / 2 - 1 = μ + 3 / 2 by ring] at this
    rw [this]; rfl
  rw [aZero_eq_azInt]
  have hn' : ‖-(1 / 2 : ℂ) * ell‖ = 1 / 2 * ‖ell‖ := by
    rw [norm_mul, norm_neg, norm_div, norm_one]
    norm_num
  calc ‖-(1 / 2 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χ A) t‖
      = ‖-(1 / 2 : ℂ) * ell‖ * ‖∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χ A) t‖ := norm_mul _ _
    _ ≤ (1 / 2 * ‖ell‖) * (Kc * gamFac μ r) := by
        rw [hn', ← hGam]
        exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ‖ell‖ * ((1 + μ) * C0 * gamFac μ r) * affNorm as A := by
        rw [hKc]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
