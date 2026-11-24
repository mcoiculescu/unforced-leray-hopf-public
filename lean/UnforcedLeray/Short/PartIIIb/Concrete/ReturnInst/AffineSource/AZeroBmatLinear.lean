import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatLinear.Helpers

/-!
# `AZeroBmatLinear`: `A ↦ a₀(B_{μ,ν}[A])` is additive and real-homogeneous on `𝒜`

Source 4614-4618 (`a₀`), 4757-4760 (`B_{μ,ν}[A] = (A^y)' + μA^y/s`), 4812-4815, 4863-4864.
Pointwise linearity of `B` at `s > 0` is `bmatLinear` with `ayDiffAt`; the Laplace integrands
are integrable on `(0,∞)` (`integrableOn_azInt_Bmat`), so the integral is linear.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem aZeroBmatLinear (as : ℝ) (χf : ℝ → ℝ) : AZeroBmatLinear as χf := by
  intro hχ lam ell ν μ hν hμ A A' r hA hA'
  have hdiff : ∀ X : ℝ → Mat3, IsAffElem as X → ∀ t : ℝ, 0 < t →
      DifferentiableAt ℝ (Ay ν χf X) t :=
    fun X hX t ht => ayDiffAt as χf hχ ν X hX t ht
  have hadd : ∀ t : ℝ, 0 < t → azInt lam μ (Bmat ν μ χf (A + A')) t =
      azInt lam μ (Bmat ν μ χf A) t + azInt lam μ (Bmat ν μ χf A') t := by
    intro t ht
    have hB := (bmatLinear ν μ χf A A' 1 t (hdiff A hA t ht) (hdiff A' hA' t ht)).1
    unfold azInt
    rw [hB]
    simp only [Bd, Be, Pi.add_apply]
    push_cast
    ring
  have hsmul : ∀ t : ℝ, 0 < t → azInt lam μ (Bmat ν μ χf (r • A)) t =
      (r : ℂ) * azInt lam μ (Bmat ν μ χf A) t := by
    intro t ht
    have hB := (bmatLinear ν μ χf A A r t (hdiff A hA t ht) (hdiff A hA t ht)).2
    unfold azInt
    rw [hB]
    simp only [Bd, Be, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  constructor
  · rw [aZero_eq_azInt, aZero_eq_azInt, aZero_eq_azInt]
    have key : ∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf (A + A')) t =
        (∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf A) t) +
          ∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf A') t := by
      rw [← integral_add (integrableOn_azInt_Bmat hχ μ hν hμ lam A hA)
        (integrableOn_azInt_Bmat hχ μ hν hμ lam A' hA')]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hadd t ht)
    rw [key]
    ring
  · rw [aZero_eq_azInt, aZero_eq_azInt]
    have key : ∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf (r • A)) t =
        (r : ℂ) * ∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf A) t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hsmul t ht
    rw [key]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
