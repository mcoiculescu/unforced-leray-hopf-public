import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8`: the oscillating part of the cylinder pressure (conditional)

Source of record: `the November 2 reference manuscript`, lines 276-288.

`cylPoisOscPartBound_of` derives `CylPoisOscPartBound` (`|q - \bar q| ≤ M₁(c,K)` when `|Δq| ≤ K`)
from the six leaves `CylPoisModeC2`, `CylPoisModeLaplace`, `CylPoisQModeEstimates`,
`CylPoisMaxPrinciple`, `CylPoisFourierPointwise`, `CylPoisQAvgReal` (`Sub/T02_3_8.lean`).  For
`n ≠ 0` the mode `m_n` of `q` is `C²`, decays, and solves `m_n'' - λ_n² m_n = (Δq)_n` with
`λ_n = 2π|n|/c` and `‖(Δq)_n‖ ≤ K' = max K 0`; the maximum principle gives
`‖m_n‖ ≤ 2K'/λ_n² = a / n²` with `a = K' c² / (2π²)`; the Fourier series then gives
`|q - \bar q| ≤ a ∑_n 1/n²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **The oscillating part from its six leaves.** -/
theorem cylPoisOscPartBound_of (h1 : CylPoisModeC2) (h2 : CylPoisModeLaplace)
    (h3 : CylPoisQModeEstimates) (h4 : CylPoisMaxPrinciple) (h5 : CylPoisFourierPointwise)
    (h6 : CylPoisQAvgReal) : CylPoisOscPartBound := by
  intro c K hc
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = max K 0 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := hK'def ▸ le_max_right _ _
  have hKK' : K ≤ K' := hK'def ▸ le_max_left _ _
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = K' * c ^ 2 / (2 * Real.pi ^ 2) := ⟨_, rfl⟩
  have ha : 0 ≤ a := by rw [hadef]; positivity
  refine ⟨a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2, fun q hq hqp hq0 hK z => ?_⟩
  -- the complexified function
  have hf2 : ContDiff ℝ 2 (fun w : Plane => ((q w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hfper : Cyl.IsPeriodic c (fun w : Plane => ((q w : ℝ) : ℂ)) := fun w => by
    simp only [hqp w]
  have hfdec : Tendsto (fun w : Plane => ((q w : ℝ) : ℂ))
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hq0
    rw [Complex.ofReal_zero] at h
    exact h
  -- the Laplacian is bounded by `K'`
  have hsrc : ∀ w : Plane, ‖((Train.lapS q w : ℝ) : ℂ)‖ ≤ K' := fun w => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hK w).trans hKK'
  -- the bound on every non-zero mode
  have hmode : ∀ (η : ℝ) (n : ℤ), n ≠ 0 →
      ‖Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) η‖ ≤ a / (n : ℝ) ^ 2 := by
    intro η n hn
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hc0 : c ≠ 0 := hc.ne'
    obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = 2 * Real.pi * |(n : ℝ)| / c := ⟨_, rfl⟩
    have hlam : 0 < lam := by
      rw [hlamdef]
      have : 0 < |(n : ℝ)| := abs_pos.2 hn'
      positivity
    have hlam2 : lam ^ 2 = (2 * Real.pi * n / c) ^ 2 := by
      rw [hlamdef, div_pow, div_pow, mul_pow, mul_pow, sq_abs]
      ring
    obtain ⟨hm2, hm''⟩ := h1 c hc n _ hf2
    have hlap : ∀ e, ‖deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e
        - ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e‖
          ≤ K' := by
      intro e
      have hL := h2 c hc n q hq hqp hn e
      have hEq : deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e
          - ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e
          = Cyl.qMode c hc n (fun w => ((Train.lapS q w : ℝ) : ℂ)) e := by
        rw [hm'' e, hL, hlam2]
      rw [hEq]
      exact (h3 c hc n _).1 K' hsrc e
    have hdec := (h3 c hc n _).2 hfdec
    have hbound := h4 _ lam K' hm2 hlam hlap hdec η
    refine hbound.trans (le_of_eq ?_)
    rw [hlam2, hadef]
    field_simp
  -- Fourier inversion
  have hA : Summable (fun n : ℤ => a / (n : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    refine (h.mul_left a).congr (fun n => ?_)
    rw [mul_one_div]
  have hA0 : ∀ n : ℤ, 0 ≤ a / (n : ℝ) ^ 2 := fun n => div_nonneg ha (sq_nonneg _)
  have hres := h5 c hc (fun w : Plane => ((q w : ℝ) : ℂ)) (fun n : ℤ => a / (n : ℝ) ^ 2) z.2
    hf2.continuous hfper hA hA0 (fun n hn => hmode z.2 n hn) z.1
  have hsum : ∑' n : ℤ, a / (n : ℝ) ^ 2 = a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by rw [mul_one_div])
  have hq0m : Cyl.qMode c hc 0 (fun w : Plane => ((q w : ℝ) : ℂ)) z.2
      = ((hmean c q z.2 : ℝ) : ℂ) := by
    rw [Cyl.qMode_zero hc]
    exact h6 c q z.2
  have hres2 : ‖((q z : ℝ) : ℂ) - Cyl.qMode c hc 0 (fun w : Plane => ((q w : ℝ) : ℂ)) z.2‖
      ≤ ∑' n : ℤ, a / (n : ℝ) ^ 2 := hres
  rw [hq0m, hsum] at hres2
  calc |q z - hmean c q z.2| = ‖((q z : ℝ) : ℂ) - ((hmean c q z.2 : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := hres2

end UnforcedLeray.Short.PartI
