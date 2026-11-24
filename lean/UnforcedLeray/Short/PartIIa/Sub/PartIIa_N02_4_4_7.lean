import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

/-!
# Part II-a, task `PartII-a:N02/4/4/7` (`NzFpParseval`): decomposition into lemma Props

Source of record: `the November 2 reference manuscript`, lines 1713-1727 and 1744-1745
(finite Fourier sums in `q`; orthogonality of the modes on one period `(0, c]`).

`measureH c = (s^{-3/2} ds dq dη)` restricted to `cell c = (0,∞) × (0, c] × ℝ`.  For a finite mode sum
`Σ e_n(q) g_n(s, η)` the proof is: `opS^[α]` acts coefficientwise (`NzFpOpSIter`), the weighted
`‖·‖²` is dominated by a sum of `q`-independent integrable terms (`NzFpOneModeInt`, `NzFpProdInt`),
the integral over `measureH c` is the iterated integral with `q` innermost (`NzFpHFubini`), and the
inner `q`-integral is `c Σ ‖w_n‖²` (`NzFpQScalar`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Scalar `q`-Parseval** (lines 1744-1745): `∫_0^c ‖Σ e^{2π i n q/c} z_n‖² dq = c Σ ‖z_n‖²` for
complex numbers `z_n` (the scalar case of `NzQParseval`, with `v_n = (z_n, 0)`). -/
def NzFpQScalar : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (z : ℤ → ℂ),
    ∫ q in (0 : ℝ)..c,
        ‖∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • z n‖ ^ 2 =
      c * ∑ n ∈ M, ‖z n‖ ^ 2

/-- **Fubini on `measureH c` with `q` innermost**: for `G` integrable on `measureH c`,
`∫ G d(measureH c) = ∫_{(s,η) ∈ (0,∞)×ℝ} s^{-3/2} (∫_0^c G(s, q, η) dq) d(s,η)`
(`measureH c` is `s^{-3/2} ds dq dη` on `(0,∞) × (0,c] × ℝ`; use `IntegralMeasureHCell`-style
`B0226`/`ZeroWindowBoundAux.measureH_integral_real` and reorder the three-fold product). -/
def NzFpHFubini : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ G : Profile → ℝ, Integrable G (measureH c) →
    ∫ p, G p ∂(measureH c) =
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, x.1 ^ (-(3 / 2 : ℝ)) * ∫ q in (0 : ℝ)..c, G (x.1, q, x.2)

/-- **A `q`-independent function is integrable on `measureH c` when its two-variable weighted version
is integrable on the strip** `(0,∞) × ℝ`: `Integrable (H ∘ (p.1, p.2.2)) (measureH c)` from
`IntegrableOn (H x * x.1^{-3/2}) ((0,∞) ×ˢ univ)` (the `q`-interval `(0, c]` has finite length). -/
def NzFpProdInt : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ H : ℝ × ℝ → ℝ, Continuous H →
    IntegrableOn (fun x : ℝ × ℝ => H x * x.1 ^ (-(3 / 2 : ℝ))) (Ioi 0 ×ˢ univ) →
    Integrable (fun p : Profile => H (p.1, p.2.2)) (measureH c)

/-- **Integrability of the one-mode moments on the strip**: for `NzDecay1 g` (band `s ∈ [s0, s1]`,
`s0 > 0`, and `g`, `∂_s g` bounded by `C e^{-κ|η|}`) and `α, j ∈ {0, 1}`, the function
`(|η|^j)² ‖(nzS2^[α] g)(s, η)‖² s^{-3/2}` is integrable on `(0,∞) × ℝ` (`s^{-3/2} ≤ s0^{-3/2}` on the
band, `‖nzS2 g‖ ≤ s1 C e^{-κ|η|}`, `∫ (1 + η²) e^{-2κ|η|} < ∞`). -/
def NzFpOneModeInt : Prop :=
  ∀ g : ℝ × ℝ → ℂ, NzDecay1 g → ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
    IntegrableOn (fun x : ℝ × ℝ => (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (Ioi 0 ×ˢ univ)

/-- `nzS2 g = s ∂_s g` is smooth when `g` is. -/
def NzFpS2Smooth : Prop :=
  ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → ContDiff ℝ ∞ (nzS2 g)

/-- `opS^[α]` of a finite mode sum is the mode sum of `nzS2^[α]` (`α ∈ {0,1}`; for `α = 1` this is
`nzfpOpSModeSum`). -/
def NzFpOpSIter : Prop :=
  ∀ (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ), (∀ n ∈ M, ContDiff ℝ ∞ (g n)) →
    ∀ α ∈ Finset.range 2, ∀ p : Profile,
      (opS^[α] (nzModeSum c M g)) p = ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          (nzS2^[α] (g n)) (p.1, p.2.2)


/-- `‖·‖²`-weighted moment squared equals the integral (the moment is a square root of a nonnegative
integral). -/
theorem nzfpMom2_sq (j α : ℕ) (g : ℝ × ℝ → ℂ) :
    nzMom2 j α g ^ 2 = ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
  have hI : 0 ≤ ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine setIntegral_nonneg (measurableSet_Ioi.prod MeasurableSet.univ) ?_
    intro x hx
    have : 0 < x.1 := hx.1
    positivity
  unfold nzMom2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

/-- **`NzFpParseval` from the lemma Props.** -/
theorem nzFpParseval_of (h1 : NzFpQScalar) (h2 : NzFpHFubini) (h3 : NzFpOneModeInt)
    (h3b : NzFpProdInt) (h4 : NzFpOpSIter) (h5 : NzFpS2Smooth) : NzFpParseval := by
  intro c hc M g hg
  have hgs : ∀ n ∈ M, ContDiff ℝ ∞ (g n) := fun n hn => (hg n hn).1
  have hw : ∀ α ∈ Finset.range 2, ∀ n ∈ M, ContDiff ℝ ∞ (nzS2^[α] (g n)) := by
    intro α hα n hn
    have : α = 0 ∨ α = 1 := by simp at hα; omega
    rcases this with rfl | rfl
    · simpa using hgs n hn
    · simpa using h5 _ (hgs n hn)
  -- the main computation, for fixed `α, j`
  have main : ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
      Integrable (fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖(opS^[α] (nzModeSum c M g)) p‖ ^ 2)
        (measureH c) ∧
      nzSq c α j (nzModeSum c M g) = c * ∑ n ∈ M, nzMom2 j α (g n) ^ 2 := by
    intro α hα j hj
    set w : ℤ → ℝ × ℝ → ℂ := fun n => nzS2^[α] (g n) with hwdef
    have hT := h4 c M g hgs α hα
    have hwc : ∀ n ∈ M, Continuous (w n) := fun n hn => (hw α hα n hn).continuous
    -- integrable one-mode pieces
    have hint : ∀ n ∈ M, Integrable
        (fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖w n (p.1, p.2.2)‖ ^ 2) (measureH c) := by
      intro n hn
      refine h3b c hc (fun x => (|x.2| ^ j) ^ 2 * ‖w n x‖ ^ 2) ?_ (h3 (g n) (hg n hn) α hα j hj)
      have := hwc n hn
      fun_prop
    set F : Profile → ℝ := fun p => (|p.2.2| ^ j) ^ 2 * ‖(opS^[α] (nzModeSum c M g)) p‖ ^ 2 with hF
    have hFeq : F = fun p => (|p.2.2| ^ j) ^ 2 * ‖∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          w n (p.1, p.2.2)‖ ^ 2 := by
      funext p; simp only [hF, hT p, hwdef]
    have hFc : Continuous F := by
      rw [hFeq]
      have : ∀ n ∈ M, Continuous (fun p : Profile =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
            w n (p.1, p.2.2)) := by
        intro n hn
        have := hwc n hn
        fun_prop
      have hs := continuous_finsetSum M this
      fun_prop
    have hFint : Integrable F (measureH c) := by
      have hbd : Integrable (fun p : Profile => (M.card : ℝ) * ∑ n ∈ M,
          (|p.2.2| ^ j) ^ 2 * ‖w n (p.1, p.2.2)‖ ^ 2) (measureH c) :=
        (integrable_finsetSum M hint).const_mul _
      refine hbd.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
      rw [hFeq]
      simp only
      rw [Real.norm_of_nonneg (by positivity)]
      have h1' : ‖∑ n ∈ M,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
            w n (p.1, p.2.2)‖ ^ 2 ≤ (M.card : ℝ) * ∑ n ∈ M, ‖w n (p.1, p.2.2)‖ ^ 2 := by
        have hn : ‖∑ n ∈ M,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
              w n (p.1, p.2.2)‖ ≤ ∑ n ∈ M, ‖w n (p.1, p.2.2)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_smul]
          have : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))‖
              = 1 := by
            rw [Complex.norm_exp]
            simp
          rw [this, one_mul]
        calc _ ≤ (∑ n ∈ M, ‖w n (p.1, p.2.2)‖) ^ 2 := by gcongr
          _ ≤ _ := sq_sum_le_card_mul_sum_sq
      calc (|p.2.2| ^ j) ^ 2 * ‖∑ n ∈ M,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
              w n (p.1, p.2.2)‖ ^ 2
          ≤ (|p.2.2| ^ j) ^ 2 * ((M.card : ℝ) * ∑ n ∈ M, ‖w n (p.1, p.2.2)‖ ^ 2) := by
            gcongr
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; 
                    refine Finset.sum_congr rfl fun n _ => ?_; ring
    refine ⟨hFint, ?_⟩
    -- Fubini and Parseval
    unfold nzSq
    show ∫ p, F p ∂(measureH c) = _
    rw [h2 c hc F hFint]
    have hinner : ∀ x : ℝ × ℝ, ∫ q in (0 : ℝ)..c, F (x.1, q, x.2) =
        (|x.2| ^ j) ^ 2 * (c * ∑ n ∈ M, ‖w n x‖ ^ 2) := by
      intro x
      rw [hFeq]
      simp only
      rw [intervalIntegral.integral_const_mul, h1 c hc M (fun n => w n x)]
    simp_rw [hinner]
    have hrw : ∀ x : ℝ × ℝ, x.1 ^ (-(3 / 2 : ℝ)) * ((|x.2| ^ j) ^ 2 * (c * ∑ n ∈ M, ‖w n x‖ ^ 2)) =
        c * ∑ n ∈ M, (|x.2| ^ j) ^ 2 * ‖w n x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
      intro x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    simp_rw [hrw]
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum M (fun n hn => h3 (g n) (hg n hn) α hα j hj)]
    exact Finset.sum_congr rfl fun n _ => (nzfpMom2_sq j α (g n)).symm
  exact ⟨fun α hα j hj => (main α hα j hj).1, fun α hα j hj => (main α hα j hj).2⟩

end UnforcedLeray.Short.PartIIa
