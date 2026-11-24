import UnforcedLeray.Short.PartIIIa.FlatCausal
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real parts of causal energy solutions (bridge for `nearD0Surj_of`, source 3420-3440, 3560-3581)

Source of record: `the November 2 reference manuscript` (73 pages).

The near spaces `H`, `Z` of `Concrete/Spaces.lean` are real (source 2664-2701, 3866-3872), while
the flat causal equation of `PartIII-a/FlatCausal.lean` is stated for complex fields.  The equation
`b_s + (μ/s)b - νΔb + 𝒫₀div(v⊗b + b⊗v) = 𝒫₀div F` (source 3420-3424) has real coefficients when
`μ` is real (the near exponent `μ ∈ K ⊂ (0, 1/4)`, source 3866-3880) and `v` is real, and it is
tested against real fields, so the componentwise real part of a solution solves the equation with
the real part of the force.  All clauses of `IsCausalEnergySolution` pass to real parts:
the energy integrands decrease (`|Re z| ≤ |z|`), and the cell pairings are integrable because
`HasWeakCellDerivC` (the `weakGrad` clause) contains their integrability, so integral and real
part commute.

* `reVecC`, `reTenC` : componentwise real parts of complex planar vector and tensor fields;
* `flatIntegrand_re` : `flatIntegrand` of the real parts is the real part of `flatIntegrand`;
* `isCausalEnergySolution_re` : real parts of a causal energy solution (real `μ`, any real
  coefficient `vel`) form a causal energy solution with the real part of the force;
* `vnorm2_reVecC_le`, `tnorm2_reTenC_le` : `|Re z| ≤ |z|` for the planar norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.IIIa

/-- Componentwise real part of a complex planar vector field, as a complex field. -/
def reVecC (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ × (ℝ × ℝ) → Fin 2 → ℂ :=
  fun p i => (((b p i).re : ℝ) : ℂ)

/-- Componentwise real part of a complex planar tensor field, as a complex field. -/
def reTenC (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
  fun p i j => (((F p i j).re : ℝ) : ℂ)

theorem sq_re_le_sq_norm (z : ℂ) : ‖((z.re : ℝ) : ℂ)‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2

/-- `|Re b| ≤ |b|` for the Euclidean norm of a planar vector. -/
theorem vnorm2_reVecC_le (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    vnorm2 (reVecC b p) ≤ vnorm2 (b p) := by
  unfold vnorm2 reVecC
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => sq_re_le_sq_norm (b p i))

/-- `|Re T| ≤ |T|` for the Frobenius norm of a planar tensor. -/
theorem tnorm2_reTenC_le (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (reTenC T p) ≤ tnorm2 (T p) := by
  unfold tnorm2 reTenC
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => sq_re_le_sq_norm (T p i j))

theorem measurable_reVecC {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hb : ∀ i, Measurable fun p => b p i)
    (i : Fin 2) : Measurable fun p => reVecC b p i :=
  (Complex.measurable_re.comp (hb i)).complex_ofReal

theorem measurable_reTenC {T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ i j, Measurable fun p => T p i j) (i j : Fin 2) : Measurable fun p => reTenC T p i j :=
  (Complex.measurable_re.comp (hT i j)).complex_ofReal

/-- `Re(z · r) = Re z · r` for real `r`, as complex numbers. -/
theorem re_mul_ofReal (z : ℂ) (r : ℝ) :
    ((((z * (r : ℂ)).re : ℝ)) : ℂ) = ((z.re : ℝ) : ℂ) * (r : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  simp [Complex.mul_re]

/-- The tested equation of the real parts is the real part of the tested equation (real `μ`,
real coefficient `vel`, real test `Φ`). -/
theorem flatIntegrand_re (ν μr : ℝ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν (μr : ℂ) vel (reTenC F) (reVecC b) Φ p =
      (((flatIntegrand ν (μr : ℂ) vel F b Φ p).re : ℝ) : ℂ) := by
  have hdiv : ((μr : ℂ) / (p.1 : ℂ)) = (((μr / p.1 : ℝ)) : ℂ) := by push_cast; ring
  simp only [flatIntegrand, reTenC, reVecC, hdiv, Fin.sum_univ_two]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    ring

theorem flatIntegrand_re_fun (ν μr : ℝ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) :
    flatIntegrand ν (μr : ℂ) vel (reTenC F) (reVecC b) Φ =
      fun p => (((flatIntegrand ν (μr : ℂ) vel F b Φ p).re : ℝ) : ℂ) :=
  funext (flatIntegrand_re ν μr vel F b Φ)

/-- `∫ Re f = Re ∫ f` for an integrable complex function, as complex numbers. -/
theorem setIntegral_re_ofReal {α : Type*} [MeasurableSpace α] {m : Measure α} {s : Set α}
    {f : α → ℂ} (hf : IntegrableOn f s m) :
    ∫ x in s, (((f x).re : ℝ) : ℂ) ∂m = ((((∫ x in s, f x ∂m).re : ℝ)) : ℂ) := by
  rw [integral_complex_ofReal]
  congr 1
  exact integral_re hf

/-- **Real parts of a causal energy solution** (source 3420-3440): for real `μ` and a real
coefficient `vel`, `(Re b, Re G)` is a causal zero-entrance energy solution with force `Re F`. -/
theorem isCausalEnergySolution_re {c ν μr : ℝ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (h : IsCausalEnergySolution c ν (μr : ℂ) vel F b G) :
    IsCausalEnergySolution c ν (μr : ℂ) vel (reTenC F) (reVecC b) (reTenC G) where
  measurable := measurable_reVecC h.measurable
  gradMeasurable := measurable_reTenC h.gradMeasurable
  energyLoc s₁ s₂ h1 h2 := by
    refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_)
      (h.energyLoc s₁ s₂ h1 h2)
    have hv := vnorm2_reVecC_le b p
    have ht := tnorm2_reTenC_le G p
    have hv0 : 0 ≤ vnorm2 (reVecC b p) := Real.sqrt_nonneg _
    have ht0 : 0 ≤ tnorm2 (reTenC G p) := Real.sqrt_nonneg _
    exact add_le_add (pow_le_pow_left₀ hv0 hv 2) (pow_le_pow_left₀ ht0 ht 2)
  zeroEntrance := by
    obtain ⟨δ, hδ, hfin⟩ := h.zeroEntrance
    refine ⟨δ, hδ, lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) hfin⟩
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (vnorm2_reVecC_le b p) 2
  divFree s hs ψ hψ := by
    have hi0 := ((h.weakGrad s hs 0 0).1 ψ hψ).1
    have hi1 := ((h.weakGrad s hs 1 1).1 ψ hψ).1
    have hsum : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := hi0.add hi1
    have hpt : (fun x => reVecC b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        reVecC b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = fun x =>
          ((((b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)).re : ℝ)) :
            ℂ) := by
      funext x
      rw [Complex.add_re, Complex.ofReal_add, re_mul_ofReal, re_mul_ofReal]
      rfl
    rw [hpt, setIntegral_re_ofReal hsum, h.divFree s hs ψ hψ]
    simp
  weakGrad s hs i j := by
    have hw := h.weakGrad s hs i j
    have hpt1 : ∀ ψ : ℝ × ℝ → ℝ, (fun x => reVecC b (s, x) i * (B0579.pd j ψ x : ℂ)) =
        fun x => ((((b (s, x) i * (B0579.pd j ψ x : ℂ)).re : ℝ)) : ℂ) := fun ψ => by
      funext x; rw [re_mul_ofReal]; rfl
    have hpt2 : ∀ ψ : ℝ × ℝ → ℝ, (fun x => reTenC G (s, x) i j * (ψ x : ℂ)) =
        fun x => ((((G (s, x) i j * (ψ x : ℂ)).re : ℝ)) : ℂ) := fun ψ => by
      funext x; rw [re_mul_ofReal]; rfl
    refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · rw [hpt1 ψ]
      exact ((hw.1 ψ hψ).1.re).ofReal
    · rw [hpt2 ψ]
      exact ((hw.1 ψ hψ).2.re).ofReal
    · rw [hpt1 ψ, hpt2 ψ, setIntegral_re_ofReal (hw.1 ψ hψ).1,
        setIntegral_re_ofReal (hw.1 ψ hψ).2, hw.2 ψ hψ, Complex.neg_re, Complex.ofReal_neg]
  integrable Φ hΦ := by
    rw [flatIntegrand_re_fun]
    exact ((h.integrable Φ hΦ).re).ofReal
  weak Φ hΦ := by
    rw [flatIntegrand_re_fun, setIntegral_re_ofReal (h.integrable Φ hΦ), h.weak Φ hΦ]
    simp

end UnforcedLeray.Short.PartIIIb.NearInst
