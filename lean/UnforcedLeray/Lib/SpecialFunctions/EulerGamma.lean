import UnforcedLeray.Lib.SpecialFunctions.HolomorphicIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# The Euler integral with a complex rate (INF20 T20.1 = ExternalInputs E1)

Blueprint target INF20 T20.1, which is ExternalInputs E1 (DLMF 5.2(i), `dlmf-gamma`; scoping
notes `INF19-INF20-INF29-INF30-Algebra.md` §5 Level 3 and `ExternalInputs.md` §5.2 E1).
Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` (`Gamma/Basic.lean:372`) has a complex
exponent but a **real** rate. The manuscript needs a complex rate `λ` with `Re λ > 0`:

* tex 2009–2017, `eq:st18-t00112`, unit B0133:
  `∫_0^∞ t^{μ+3/2} e^{-λt} dt = Γ(μ+5/2) λ^{-(μ+5/2)}`, "using the logarithm of λ in the right
  half-plane", first for real `λ > 0` and then "by holomorphic continuation in Re λ > 0";
* tex 12647–12671 (`eq:affine-4-106`, B0868) and 13086–13113 (`lemma:st18-4-B`, B0872): the same
  integral `L(ζ) = ℓ(H₀) Γ(ζ+5/2) / λ^{ζ+5/2}`;
* tex 13197–13205 (B0881): `Γ(ζ+5/2) ≠ 0` and `λ^{ζ+5/2} ≠ 0`, so `L ≠ 0`.

Route (scoping bypass B7): both sides are holomorphic in `w` on the right half-plane, which is
convex, hence preconnected; they agree on `(0, ∞)` by the real-rate lemma; the identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` concludes. The left side is holomorphic by
`differentiableOn_integral_of_holomorphic` (T20.2) with the majorant `t^{Re a - 1} e^{-(Re w₀/2) t}`.
The principal branch of `w ^ (-a)` is the right-half-plane branch, because `Re w > 0` puts `w` in
the slit plane. Every integral below is of an integrable function
(`integrableOn_cpow_mul_cexp_neg_mul_Ioi`), so no junk value of the Bochner integral enters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology Complex

namespace UnforcedLeray.Special

/-- The open right half-plane `{w : ℂ | 0 < Re w}`. -/
def rightHalfPlane : Set ℂ := {w | 0 < w.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- `t ^ s e^{-bt}` is integrable on `(0, ∞)` for `s > -1`, `b > 0` (real form, from
`integrableOn_rpow_mul_exp_neg_mul_rpow` with `p = 1`). -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem measurable_cpow_mul_cexp (a w : ℂ) :
    Measurable (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(w * t))) := by
  fun_prop

/-- The modulus of the Euler integrand: `|t^{a-1} e^{-wt}| = t^{Re a - 1} e^{-(Re w) t}`, `t > 0`. -/
theorem norm_cpow_mul_cexp {a w : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (a - 1) * cexp (-(w * t))‖ = t ^ (a.re - 1) * Real.exp (-(w.re * t)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  simp

/-- The Euler integrand with complex exponent `a - 1` (`Re a > 0`) and complex rate `w`
(`Re w > 0`) is integrable on `(0, ∞)` (INF20 T20.1; tex 1994–2017, B0133). -/
theorem integrableOn_cpow_mul_cexp_neg_mul_Ioi {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(w * t))) (Ioi 0) := by
  refine Integrable.mono'
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (s := a.re - 1) (by linarith) hw)
    (measurable_cpow_mul_cexp a w).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  rw [norm_cpow_mul_cexp ht]

/-- The Euler integral is holomorphic in the rate on the right half-plane (INF20 T20.1, through
T20.2). -/
theorem differentiableOn_integral_cpow_mul_cexp {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(w * t))) rightHalfPlane := by
  refine differentiableOn_integral_of_holomorphic isOpen_rightHalfPlane
    (fun w _ => (measurable_cpow_mul_cexp a w).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_) fun w₀ hw₀ => ?_
  · exact Differentiable.differentiableOn (by fun_prop)
  · have hw₀' : 0 < w₀.re := hw₀
    refine ⟨w₀.re / 2, half_pos hw₀', fun t => t ^ (a.re - 1) * Real.exp (-(w₀.re / 2 * t)),
      integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) (half_pos hw₀'), ?_⟩
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht w hw => ?_
    have ht' : 0 < t := ht
    rw [norm_cpow_mul_cexp ht']
    have hre : w₀.re / 2 < w.re := by
      have h1 : |w.re - w₀.re| < w₀.re / 2 := by
        calc |w.re - w₀.re| = |(w - w₀).re| := by simp
          _ ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
          _ < w₀.re / 2 := by simpa [dist_eq_norm] using hw
      linarith [(abs_lt.1 h1).1]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht'.le _)
    nlinarith

/-- For a positive real `r`, `(1/r)^a = r^{-a}` (principal branch). -/
theorem one_div_ofReal_cpow {r : ℝ} (hr : 0 < r) (a : ℂ) :
    (1 / (r : ℂ)) ^ a = (r : ℂ) ^ (-a) := by
  rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact
    (Real.pi_pos).ne), Complex.cpow_neg]

/-- **The Euler integral with complex rate** (INF20 T20.1 = ExternalInputs E1; DLMF 5.2(i);
tex 2009–2017 `eq:st18-t00112`, unit B0133; tex 12647–12671, B0868; tex 13086–13113, B0872).
For `Re a > 0` and `Re w > 0`,
`∫_0^∞ t^{a-1} e^{-wt} dt = Γ(a) w^{-a}`, with the principal (right-half-plane) branch of
`w^{-a}`. -/
theorem integral_cpow_mul_cexp_neg_mul_Ioi {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(w * t)) = Gamma a * w ^ (-a) := by
  have hf := (differentiableOn_integral_cpow_mul_cexp ha).analyticOnNhd isOpen_rightHalfPlane
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => Gamma a * w ^ (-a)) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_rightHalfPlane
    exact ((differentiableAt_id.cpow_const (mem_slitPlane_iff.2 (Or.inl hw))).const_mul
      _).differentiableWithinAt
  have hreal : ∀ r : ℝ, 0 < r →
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * t))) =
        Gamma a * (r : ℂ) ^ (-a) := by
    intro r hr
    rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr, one_div_ofReal_cpow hr, mul_comm]
  have hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := Complex.continuous_ofReal.tendsto 1
      rw [Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa [Set.mem_compl_iff, Complex.ofReal_eq_one] using hr
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(w * t))) z =
        (fun w : ℂ => Gamma a * w ^ (-a)) z := by
    refine hT.frequently ?_
    have hev : ∀ᶠ r in 𝓝[≠] (1 : ℝ), 0 < r :=
      eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds one_pos)
    exact (hev.mono fun r hr => hreal r hr).frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_rightHalfPlane
    (show (1 : ℂ) ∈ rightHalfPlane by simp [rightHalfPlane]) hfreq hw

/-- **Nonvanishing of the Euler value** (INF20 T20.1 = E1; DLMF 5.2(i): Γ has no zeros; tex
2017–2018, B0133; tex 13197–13205, B0881): `Γ(a) w^{-a} ≠ 0` for `Re a > 0`, `Re w > 0`. -/
theorem gamma_mul_cpow_ne_zero {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) :
    Gamma a * w ^ (-a) ≠ 0 := by
  refine mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos ha) ?_
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  rintro rfl
  simp at hw

/-- The Laplace integral of `eq:st18-t00112` (tex 2009–2017, B0133; tex 12647–12671, B0868):
`∫_0^∞ t^{μ+3/2} e^{-λt} dt = Γ(μ+5/2) λ^{-(μ+5/2)}` for `Re μ > -5/2`, `Re λ > 0`. -/
theorem integral_cpow_mul_cexp_laplace {μ lam : ℂ} (hμ : -5 / 2 < μ.re) (hlam : 0 < lam.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (μ + 3 / 2) * cexp (-(lam * t)) =
      Gamma (μ + 5 / 2) * lam ^ (-(μ + 5 / 2)) := by
  have hre : 0 < (μ + 5 / 2).re := by
    have : (μ + 5 / 2).re = μ.re + 5 / 2 := by simp
    rw [this]; linarith
  have h := integral_cpow_mul_cexp_neg_mul_Ioi hre hlam
  rwa [show μ + 5 / 2 - 1 = μ + 3 / 2 by ring] at h

/-- The Laplace coefficient `μ ↦ Γ(μ+5/2) λ^{-(μ+5/2)}` is holomorphic on `Re μ > -5/2`
(INF20 T20.1; tex 2019–2022, B0134; tex 13197–13205, B0881). -/
theorem differentiableOn_laplaceCoeff {lam : ℂ} (hlam : lam ≠ 0) :
    DifferentiableOn ℂ (fun μ : ℂ => Gamma (μ + 5 / 2) * lam ^ (-(μ + 5 / 2)))
      {μ | -5 / 2 < μ.re} := by
  intro μ hμ
  have hμ' : -5 / 2 < μ.re := hμ
  have hre : 0 < (μ + 5 / 2).re := by
    have : (μ + 5 / 2).re = μ.re + 5 / 2 := by simp
    rw [this]; linarith
  have hG : DifferentiableAt ℂ Gamma (μ + 5 / 2) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    rw [hm] at hre
    simp at hre
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hG' : DifferentiableAt ℂ (fun μ : ℂ => Gamma (μ + 5 / 2)) μ :=
    hG.comp μ (differentiableAt_id.add_const _)
  have hP : DifferentiableAt ℂ (fun μ : ℂ => lam ^ (-(μ + 5 / 2))) μ :=
    ((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hlam)
  exact (hG'.mul hP).differentiableWithinAt

/-- The Laplace coefficient does not vanish on `Re μ > -5/2` when `Re λ > 0` (tex 2017–2018,
B0133; tex 13197–13205, B0881). The manuscript uses it on `Re μ > -3/2`. -/
theorem laplaceCoeff_ne_zero {μ lam : ℂ} (hμ : -5 / 2 < μ.re) (hlam : 0 < lam.re) :
    Gamma (μ + 5 / 2) * lam ^ (-(μ + 5 / 2)) ≠ 0 := by
  have hre : 0 < (μ + 5 / 2).re := by
    have : (μ + 5 / 2).re = μ.re + 5 / 2 := by simp
    rw [this]; linarith
  exact gamma_mul_cpow_ne_zero hre hlam

end UnforcedLeray.Special

namespace UnforcedLeray.ExternalInputs

/-- ExternalInputs E1 (DLMF 5.2(i)): the Euler integral with complex rate. Same statement as
`UnforcedLeray.Special.integral_cpow_mul_cexp_neg_mul_Ioi` (INF20 T20.1). -/
theorem integral_cpow_mul_cexp_neg_mul_Ioi {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (z - 1) * Complex.exp (-(w * t)) =
      Complex.Gamma z * w ^ (-z) :=
  UnforcedLeray.Special.integral_cpow_mul_cexp_neg_mul_Ioi hz hw

/-- ExternalInputs E1, nonvanishing of the right side (DLMF 5.2(i)). -/
theorem gamma_mul_cpow_ne_zero {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.Gamma z * w ^ (-z) ≠ 0 :=
  UnforcedLeray.Special.gamma_mul_cpow_ne_zero hz hw

end UnforcedLeray.ExternalInputs
