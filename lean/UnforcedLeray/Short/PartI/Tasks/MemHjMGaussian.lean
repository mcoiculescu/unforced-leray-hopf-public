import UnforcedLeray.Units.B0008
import UnforcedLeray.Units.B0059.NUE.P.Infra.Sobolev.Smooth
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Part I, task `PartI:S03`: Gaussian-bounded smooth functions lie in `H^j_M`

Source of record: `the November 2 reference manuscript`, lines 593-598
(every derivative of the Gaussian seed is bounded by a polynomial times `e^{-r^2/4}`; such
functions lie in `H^j_M` for every `j` and `M`).

Proof. Take `g := ∂^α f` for `α ∈ multiIdx j`. A `C^∞` function has classical derivatives that are
weak derivatives (`NonUniqueEuler.Sob.hasWeakDerivOn_of_contDiffOn`), and
`|∂^α f(y)| ≤ ‖D^{|α|} f(y)‖` (`UnforcedLeray.B0059.NUE.Sob.norm_partialD_le_norm_iteratedFDeriv`,
the same identity as in the `PlanarBS` copy of `partialD`, which is definitionally equal).
The weight satisfies `⟨y⟩^M ≤ (1+|y|)^{⌈M⌉₊}`, and `(1+t)^K e^{-t²/4} ≤ e^{2K²} e^{-t²/8}` for
`t ≥ 0` (from `1 + t ≤ e^t`). So `⟨y⟩^M g` is dominated by a multiple of `e^{-|y|²/8}`, which is in
`L²(ℂ)` by Mathlib's complex Gaussian integrability (`GaussianFourier`).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ContDiff
open NonUniqueEuler.Sob

namespace UnforcedLeray.Short.PartI

/-- `1 ≤ ⟨y⟩`. -/
theorem s03_one_le_bracket (y : ℂ) : 1 ≤ UnforcedLeray.B0008.bracket y := by
  rw [UnforcedLeray.B0008.bracket]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖y‖])

/-- `⟨y⟩ ≤ 1 + |y|`. -/
theorem s03_bracket_le_one_add_norm (y : ℂ) : UnforcedLeray.B0008.bracket y ≤ 1 + ‖y‖ := by
  rw [UnforcedLeray.B0008.bracket, Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith [norm_nonneg y]⟩

/-- `⟨y⟩^M ≤ (1 + |y|)^{⌈M⌉₊}`. -/
theorem s03_bracket_rpow_le (M : ℝ) (y : ℂ) :
    UnforcedLeray.B0008.bracket y ^ M ≤ (1 + ‖y‖) ^ ⌈M⌉₊ := by
  calc UnforcedLeray.B0008.bracket y ^ M
      ≤ UnforcedLeray.B0008.bracket y ^ (⌈M⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (s03_one_le_bracket y) (Nat.le_ceil M)
    _ = UnforcedLeray.B0008.bracket y ^ ⌈M⌉₊ := Real.rpow_natCast _ _
    _ ≤ (1 + ‖y‖) ^ ⌈M⌉₊ :=
        pow_le_pow_left₀ (UnforcedLeray.B0008.bracket_pos y).le
          (s03_bracket_le_one_add_norm y) _

/-- `(1 + t)^K e^{-t²/4} ≤ e^{2K²} e^{-t²/8}` for `t ≥ 0`. -/
theorem s03_poly_mul_gauss (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ K * Real.exp (-(t ^ 2) / 4) ≤
      Real.exp (2 * (K : ℝ) ^ 2) * Real.exp (-(t ^ 2) / 8) := by
  have h1 : (1 + t) ^ K ≤ Real.exp t ^ K :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) K
  have h1' : Real.exp t ^ K = Real.exp ((K : ℝ) * t) := (Real.exp_nat_mul t K).symm
  have h2 : Real.exp ((K : ℝ) * t) ≤ Real.exp (t ^ 2 / 8) * Real.exp (2 * (K : ℝ) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t - 4 * (K : ℝ))]
  have h3 : Real.exp (t ^ 2 / 8) * Real.exp (-(t ^ 2) / 4) = Real.exp (-(t ^ 2) / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + t) ^ K * Real.exp (-(t ^ 2) / 4)
      ≤ (Real.exp (t ^ 2 / 8) * Real.exp (2 * (K : ℝ) ^ 2)) * Real.exp (-(t ^ 2) / 4) :=
        mul_le_mul_of_nonneg_right (h1.trans (h1'.le.trans h2)) (Real.exp_pos _).le
    _ = Real.exp (2 * (K : ℝ) ^ 2) * Real.exp (-(t ^ 2) / 8) := by
        rw [← h3]
        ring

/-- `exp(-b |y|²)` is integrable on `ℂ` for `b > 0` (real part of Mathlib's complex Gaussian). -/
theorem s03_integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℂ => Real.exp (-b * ‖y‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun y : ℂ => (Complex.exp
    (-(b : ℂ) * ‖y‖ ^ 2 + 0 * inner ℝ (0 : ℂ) y)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h

/-- `e^{-|y|²/4}` is integrable on `ℂ`. -/
theorem s03_integrable_gauss_quarter :
    Integrable (fun y : ℂ => Real.exp (-(‖y‖ ^ 2) / 4)) := by
  refine (s03_integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  ring

/-- `D e^{-|y|²/8}` is in `L²(ℂ)`. -/
theorem s03_memLp_gauss_eighth (D : ℝ) :
    MemLp (fun y : ℂ => D * Real.exp (-(‖y‖ ^ 2) / 8)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun y : ℂ => Real.exp (-(‖y‖ ^ 2) / 8)) volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hG : MemLp (fun y : ℂ => Real.exp (-(‖y‖ ^ 2) / 8)) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine s03_integrable_gauss_quarter.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  exact hG.const_mul D

/-- A continuous function with a Gaussian-polynomial bound is `⟨y⟩^M`-weighted `L²`. -/
theorem s03_memLp_weight {M : ℝ} {g : ℂ → ℂ} (hg : Continuous g) {C : ℝ} {N : ℕ}
    (hbd : ∀ y : ℂ, ‖g y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :
    MemLp (fun y : ℂ => UnforcedLeray.B0008.bracket y ^ M • g y) 2 volume := by
  have hcont : Continuous fun y : ℂ => UnforcedLeray.B0008.bracket y ^ M • g y :=
    (UnforcedLeray.B0008.continuous_bracket_rpow M).smul hg
  refine MemLp.mono' (s03_memLp_gauss_eighth
    (|C| * Real.exp (2 * ((⌈M⌉₊ + N : ℕ) : ℝ) ^ 2))) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hbr0 : 0 ≤ UnforcedLeray.B0008.bracket y ^ M :=
    Real.rpow_nonneg (UnforcedLeray.B0008.bracket_pos y).le M
  have hgb : ‖g y‖ ≤ |C| * ((1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) := by
    have h0 : 0 ≤ (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4) := by positivity
    calc ‖g y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4) := hbd y
      _ = C * ((1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) := by ring
      _ ≤ |C| * ((1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h0
  calc ‖UnforcedLeray.B0008.bracket y ^ M • g y‖
      = UnforcedLeray.B0008.bracket y ^ M * ‖g y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hbr0]
    _ ≤ (1 + ‖y‖) ^ ⌈M⌉₊ * (|C| * ((1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))) :=
        mul_le_mul (s03_bracket_rpow_le M y) hgb (norm_nonneg _)
          (pow_nonneg (by positivity) _)
    _ = |C| * ((1 + ‖y‖) ^ (⌈M⌉₊ + N) * Real.exp (-(‖y‖ ^ 2) / 4)) := by
        rw [pow_add]
        ring
    _ ≤ |C| * (Real.exp (2 * ((⌈M⌉₊ + N : ℕ) : ℝ) ^ 2) * Real.exp (-(‖y‖ ^ 2) / 8)) :=
        mul_le_mul_of_nonneg_left (s03_poly_mul_gauss _ (norm_nonneg y)) (abs_nonneg C)
    _ = |C| * Real.exp (2 * ((⌈M⌉₊ + N : ℕ) : ℝ) ^ 2) * Real.exp (-(‖y‖ ^ 2) / 8) := by
        ring

/-- The classical derivative `∂^α f` of a `C^∞` function is continuous. -/
theorem s03_partialD_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (α : ℕ × ℕ) :
    Continuous (partialD α f) := by
  have hfn : ContDiffOn ℝ (pdList α).length f univ := (contDiff_infty.1 hf _).contDiffOn
  have h := WeakDerivAux.contDiffOn_iterDirDeriv isOpen_univ hfn (pdList α) 0 (by simp)
  exact continuousOn_univ.1 h.continuousOn

/-- `|∂^α f(y)| ≤ ‖D^{|α|} f(y)‖` for a `C^∞` function. -/
theorem s03_norm_partialD_le {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (α : ℕ × ℕ) (y : ℂ) :
    ‖partialD α f y‖ ≤ ‖iteratedFDeriv ℝ (α.1 + α.2) f y‖ := by
  have h := (contDiff_infty.1 hf (α.1 + α.2)).contDiffAt (x := y)
  exact UnforcedLeray.B0059.NUE.Sob.norm_partialD_le_norm_iteratedFDeriv
    (γ := α) (f := f) (x := y) (by exact_mod_cast h)

/-- **Task `PartI:S03`** (source lines 593-598): a `C^∞` function on `ℂ ≅ ℝ²` whose derivatives
are all bounded by a polynomial times `e^{-|y|²/4}` lies in `H^j_M` for every `j` and `M`. -/
theorem memHjM_of_gaussian_bounds {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hb : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ, ‖iteratedFDeriv ℝ k f y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) (j : ℕ) (M : ℝ) : B0008.MemHjM j M f := by
  choose C N hCN using hb
  refine ⟨?_, fun α _ => ?_⟩
  · refine s03_memLp_weight (M := M) hf.continuous (C := C 0) (N := N 0) (fun y => ?_)
    have h0 := hCN 0 y
    rwa [norm_iteratedFDeriv_zero] at h0
  · have hcα : Continuous (partialD α f) := s03_partialD_continuous hf α
    refine ⟨partialD α f, s03_memLp_weight (M := M) hcα (C := C (α.1 + α.2))
      (N := N (α.1 + α.2)) (fun y => ?_), ?_⟩
    · exact (s03_norm_partialD_le hf α y).trans (hCN _ y)
    · exact hasWeakDerivOn_of_contDiffOn isOpen_univ (n := (pdList α).length) le_rfl
        (contDiff_infty.1 hf _).contDiffOn

end UnforcedLeray.Short.PartI
