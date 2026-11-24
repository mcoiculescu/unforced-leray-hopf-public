import UnforcedLeray.Analysis.WeakL2
import UnforcedLeray.Analysis.Sturm.L2TestPairing

/-!
# Complex test pairings from actual real-Hilbert weak convergence

The real L² inner product is proved to be the real part of the complex L²
inner product. Testing additionally against i times the test vector recovers
the imaginary part. Consequently the actual real-Hilbert subsequence theorem
supplies convergence of full complex distributional test integrals.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ComplexConjugate
namespace UnforcedLeray.Rayleigh
open Sturm

/-- Compatibility of the existing real and complex L² inner products. -/
theorem real_inner_complexL2 (f g : ComplexL2) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  change (∫ a : ℝ, (inner ℂ (f a) (g a)).re) =
    (∫ a : ℝ, inner ℂ (f a) (g a)).re
  simpa only [RCLike.re_eq_complex_re] using
    (integral_re (L2.integrable_inner (𝕜 := ℂ) f g))

variable {ι : Type*} {u : ι → ComplexL2} {x : ComplexL2} {l : Filter ι}

/-- The full complex inner product converges under the actual real weak topology. -/
theorem weakTendsto_complex_inner (h : WeakL2.WeakTendsto u l x) (v : ComplexL2) :
    Tendsto (fun i => inner ℂ (u i) v) l (𝓝 (inner ℂ x v)) := by
  have hr : Tendsto (fun i => (inner ℂ (u i) v).re) l (𝓝 (inner ℂ x v).re) := by
    simpa only [real_inner_complexL2] using h v
  have hi0 := h (Complex.I • v)
  simp only [real_inner_complexL2, inner_smul_right, Complex.I_mul_re] at hi0
  have hi : Tendsto (fun i => (inner ℂ (u i) v).im) l (𝓝 (inner ℂ x v).im) := by
    simpa only [neg_neg] using hi0.neg
  simpa only [Complex.re_add_im] using hr.ofReal.add (hi.ofReal.mul_const Complex.I)

/-- The order with a fixed first argument is obtained by actual complex conjugation. -/
theorem weakTendsto_complex_inner_right (h : WeakL2.WeakTendsto u l x) (v : ComplexL2) :
    Tendsto (fun i => inner ℂ v (u i)) l (𝓝 (inner ℂ v x)) := by
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp
    (weakTendsto_complex_inner h v)
  simpa only [Function.comp_def, inner_conj_symm] using hc

/-- Equivalence with the usual complex Hilbert weak convergence, without
replacing the real L² instance used by the compactness library. -/
theorem weakTendsto_iff_complex_inner :
    WeakL2.WeakTendsto u l x ↔
      ∀ v : ComplexL2, Tendsto (fun i => inner ℂ (u i) v) l (𝓝 (inner ℂ x v)) := by
  constructor
  · exact weakTendsto_complex_inner
  · intro h v
    have hr := Complex.continuous_re.continuousAt.tendsto.comp (h v)
    simpa only [real_inner_complexL2, Function.comp_def] using hr

/-- Actual bilinear integral test pairings converge for every genuine L² test.
The pairings are integrable by Hölder, as established by `integrable_mul_l2`. -/
theorem weakTendsto_integral_mul (h : WeakL2.WeakTendsto u l x)
    (φ : ℝ → ℂ) (hφ : MemLp φ 2 (volume : Measure ℝ)) :
    Tendsto (fun i => ∫ t, u i t * φ t) l (𝓝 (∫ t, x t * φ t)) := by
  have hp : Tendsto (fun i => l2Pairing φ hφ (u i)) l (𝓝 (l2Pairing φ hφ x)) := by
    simpa only [l2Pairing, innerSL_apply_apply] using
      weakTendsto_complex_inner_right h (hφ.star.toLp (star φ))
  simpa only [l2Pairing_apply] using hp

end UnforcedLeray.Rayleigh
