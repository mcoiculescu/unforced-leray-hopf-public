import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds

/-!
# Part II-b, task `PartII-b:T15/2/18`: the exact square identity in the logarithmic chart

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (the weak
product rule in the `H_2` measure, log chart `s = e^t`). The target is the Prop `LogSquareIdentity`
(`Sub/T15_2.lean`, leaf `PartII-b:T15/2/18`), proved unchanged.

Proof outline.
1. Pointwise: `Re((a - b) * conj (a + b)) = ‖a‖² - ‖b‖²`, so `Re` of the integrand is
   `h⁻¹ (‖u_h‖² - ‖u‖²) ψ`.
2. Integrability: `‖u‖²` and `‖u_h‖²` are integrable, `ψ` is bounded (`logTestBounds`), and the
   complex integrand is a product of two `L²` functions times a bounded factor.
3. Translation invariance of `logMeas c` under `x ↦ (x.1 + h, x.2)` gives
   `∫ ψ(x) ‖u(x.1 + h, x.2)‖² = ∫ ψ(x.1 - h, x.2) ‖u x‖²`.
4. Subtract and divide by `h`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Pointwise identity for the square term: `Re((a - b) \bar{(a + b)}) = ‖a‖² - ‖b‖²`. -/
theorem logSqId_pointwise (a b : ℂ) :
    ((a - b) * (starRingEnd ℂ) (a + b)).re = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **Leaf `PartII-b:T15/2/18`** (the exact identity behind the square term). -/
theorem logSquareIdentity : UnforcedLeray.Short.IIb.LogSquareIdentity := by
  intro c u ψ hc hu hψ h hh
  have hB : UnforcedLeray.Short.IIb.LogTestBounds := logTestBounds
  obtain ⟨⟨C, hC⟩, -, -⟩ := hB c ψ hc hψ
  have hψc : Continuous ψ := hψ.smooth.continuous
  have hψm : AEStronglyMeasurable ψ (logMeas c) := hψc.aestronglyMeasurable
  have hψCm : AEStronglyMeasurable (fun x : Coord => (ψ x : ℂ)) (logMeas c) :=
    (Complex.continuous_ofReal.comp hψc).aestronglyMeasurable
  have hψsh : Continuous (fun x : Coord => ψ (x.1 - h, x.2)) := hψc.comp (by fun_prop)
  have hψshm : AEStronglyMeasurable (fun x : Coord => ψ (x.1 - h, x.2)) (logMeas c) :=
    hψsh.aestronglyMeasurable
  have hbd : ∀ x : Coord, ‖ψ x‖ ≤ C := fun x => by rw [Real.norm_eq_abs]; exact hC x
  have hbdsh : ∀ x : Coord, ‖ψ (x.1 - h, x.2)‖ ≤ C := fun x => hbd _
  have hbdC : ∀ x : Coord, ‖(ψ x : ℂ)‖ ≤ C := fun x => by simpa using hbd x
  have hSF : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ Cyl.cellμ
    infer_instance
  -- translation `x ↦ (x.1 + h, x.2)` preserves `logMeas c`
  have hmp : MeasurePreserving (fun x : Coord => (x.1 + h, x.2)) (logMeas c) (logMeas c) :=
    (measurePreserving_add_right volume h).prod (MeasurePreserving.id (Cyl.avgμ c))
  have hemb : MeasurableEmbedding (fun x : Coord => (x.1 + h, x.2)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.addRight h)
      (MeasurableEquiv.refl (ℝ × ℝ))).measurableEmbedding
  -- `L²` facts
  have hsq : Integrable (fun x : Coord => ‖u x‖ ^ 2) (logMeas c) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hsqT : Integrable (fun x : Coord => ‖u (x.1 + h, x.2)‖ ^ 2) (logMeas c) :=
    hmp.integrable_comp_of_integrable hsq
  have hA : MemLp (fun x : Coord => u (x.1 + h, x.2)) 2 (logMeas c) :=
    hu.comp_measurePreserving hmp
  -- weighted integrability of the real parts
  have hI1 : Integrable (fun x : Coord => ψ x * ‖u x‖ ^ 2) (logMeas c) :=
    hsq.bdd_mul hψm (ae_of_all _ hbd)
  have hI2 : Integrable (fun x : Coord => ψ (x.1 - h, x.2) * ‖u x‖ ^ 2) (logMeas c) :=
    hsq.bdd_mul hψshm (ae_of_all _ hbdsh)
  have hI3 : Integrable (fun x : Coord => ψ x * ‖u (x.1 + h, x.2)‖ ^ 2) (logMeas c) :=
    hsqT.bdd_mul hψm (ae_of_all _ hbd)
  -- integrability of the complex integrand `(a - b) \bar{(a + b)} ψ`
  have hD : MemLp (fun x : Coord => u (x.1 + h, x.2) - u x) 2 (logMeas c) := hA.sub hu
  have hE : MemLp (fun x : Coord => (starRingEnd ℂ) (u (x.1 + h, x.2) + u x)) 2 (logMeas c) :=
    (hA.add hu).star
  have hPint : Integrable
      (fun x : Coord => (u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x))
      (logMeas c) := hD.integrable_mul hE
  have hQ' : Integrable
      (fun x : Coord => (ψ x : ℂ) * ((u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x)))
      (logMeas c) :=
    hPint.bdd_mul hψCm (ae_of_all _ hbdC)
  have hQ : Integrable
      (fun x : Coord => (u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ))
      (logMeas c) :=
    hQ'.congr (ae_of_all _ fun x => mul_comm _ _)
  -- pointwise real part
  have hQre : ∀ x : Coord,
      ((u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ)).re
        = (‖u (x.1 + h, x.2)‖ ^ 2 - ‖u x‖ ^ 2) * ψ x := by
    intro x
    rw [Complex.re_mul_ofReal, logSqId_pointwise]
  -- the integrand is `h⁻¹` times the `Q` integrand
  have hLHS : (fun x : Coord => ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) *
        (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ))
      = fun x : Coord => ((h⁻¹ : ℝ) : ℂ) *
          ((u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ)) := by
    funext x
    rw [Complex.real_smul]
    ring
  -- translation identity
  have htr : ∫ x, ψ x * ‖u (x.1 + h, x.2)‖ ^ 2 ∂(logMeas c)
      = ∫ x, ψ (x.1 - h, x.2) * ‖u x‖ ^ 2 ∂(logMeas c) := by
    refine Eq.trans ?_ (hmp.integral_comp hemb (fun y : Coord => ψ (y.1 - h, y.2) * ‖u y‖ ^ 2))
    congr 1
    funext x
    simp only [add_sub_cancel_right]
  -- the real part of the square term
  have hsplit : ∫ x, (‖u (x.1 + h, x.2)‖ ^ 2 - ‖u x‖ ^ 2) * ψ x ∂(logMeas c)
      = (∫ x, ψ x * ‖u (x.1 + h, x.2)‖ ^ 2 ∂(logMeas c))
        - ∫ x, ψ x * ‖u x‖ ^ 2 ∂(logMeas c) := by
    rw [← integral_sub hI3 hI1]
    congr 1
    funext x
    ring
  -- the right-hand side
  have hR : ∫ x, ((ψ (x.1 - h, x.2) - ψ x) / h) * ‖u x‖ ^ 2 ∂(logMeas c)
      = ∫ x, ((h⁻¹ : ℝ)) * (ψ (x.1 - h, x.2) * ‖u x‖ ^ 2 - ψ x * ‖u x‖ ^ 2) ∂(logMeas c) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ((ψ (x.1 - h, x.2) - ψ x) / h) * ‖u x‖ ^ 2
      = (h⁻¹ : ℝ) * (ψ (x.1 - h, x.2) * ‖u x‖ ^ 2 - ψ x * ‖u x‖ ^ 2)
    ring
  -- assemble
  have hre : (∫ x, ((u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) *
      (ψ x : ℂ)) ∂(logMeas c)).re
      = ∫ x, ((u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) *
      (ψ x : ℂ)).re ∂(logMeas c) :=
    (integral_re hQ).symm
  have hre2 : ∫ x, ((u (x.1 + h, x.2) - u x) * (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) *
      (ψ x : ℂ)).re ∂(logMeas c)
      = ∫ x, (‖u (x.1 + h, x.2)‖ ^ 2 - ‖u x‖ ^ 2) * ψ x ∂(logMeas c) :=
    integral_congr_ae (ae_of_all _ hQre)
  rw [hLHS, integral_const_mul, Complex.re_ofReal_mul, hre, hre2, hsplit, htr, hR,
    integral_const_mul, integral_sub hI2 hI1]

end UnforcedLeray.Short.IIb
