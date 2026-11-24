import UnforcedLeray.Short.PartIIb.Sub.T12_7_5
import UnforcedLeray.Short.PartIIb.Sub.T12_7_4

/-!
# Part II-b, task `PartII-b:T12/7/5/3` (`DeqPdDominate`): decomposition

Source: `the November 2 reference manuscript`,
lines 1923-1927.

Both conjuncts follow from Gaussian-tail bounds for `deqSmooth` (at the single age `s`) and for
`deqSmoothD` (uniformly for `s'` in a ball around `s`), the Gaussian integrability of a periodic
`L^r` slice (`DeqhpGaussInt`, leaf `PartII-b:T12/7/4/4`), and continuity of `deqSmooth`
(`DeqhpCont`, leaf `PartII-b:T12/7/4/1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Gaussian tail of `deqSmooth` at a fixed `s > t` (SP 1923-1927). Proof as `deqhpTail`
(`Tasks/FlatCausal/DuhamelEquation/HeatPair/Tail.lean`), which only covers `s ≤ t + 1`; adapt it to
an arbitrary fixed age `ν(s-t)`. -/
def DeqpdTailSmooth : Prop :=
  ∀ (ν t : ℝ), 0 < ν → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2,
    ∀ s : ℝ, t < s → ∃ C R a : ℝ, 0 < a ∧ ∀ z : ℝ × ℝ,
      |deqSmooth ν Ψ i t s z| ≤ C * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2)

/-- Gaussian tail of `deqSmoothD`, uniform for `s'` near `s` (SP 1923-1927): choose
`ε = (s-t)/2`, so the ages `ν(s'-t)` lie in `[ν(s-t)/2, 2ν(s-t)]`; the integrand
`cpd 0 Ψ_i + ν(cpd 1 cpd 1 Ψ_i + cpd 2 cpd 2 Ψ_i)` is bounded and supported in a fixed box, so the
bound is the same Gaussian tail estimate as in `deqhpTail`, with the worst age `2ν(s-t)`. -/
def DeqpdTailD : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2,
    ∀ s : ℝ, t < s → ∃ ε : ℝ, 0 < ε ∧ ε < s - t ∧ ∃ C R a : ℝ, 0 < a ∧
      ∀ s' ∈ Metric.ball s ε, ∀ z : ℝ × ℝ,
        |deqSmoothD ν Ψ i t s' z| ≤ C * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2)

theorem deqPdDominate_of (hc : DeqhpCont) (hG : DeqhpGaussInt) (h1 : DeqpdTailSmooth)
    (h2 : DeqpdTailD) : DeqPdDominate := by
  intro ν c r t hν ht hc0 hr g hg Ψ hΨ i s hs
  have hgi : AEStronglyMeasurable (fun z : ℝ × ℝ => g z i) volume :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable hg.2.1
  refine ⟨?_, ?_⟩
  · obtain ⟨C, R, a, ha, hb⟩ := h1 ν t hν Ψ hΨ i s hs
    have hint : Integrable (fun z : ℝ × ℝ =>
        ‖g z i‖ * (|C| * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2))) := by
      have := (hG c r hc0 hr g hg i R a ha).mul_const |C|
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [mul_assoc, mul_comm |C|]
    refine Integrable.mono' hint
      (hgi.mul ((Complex.continuous_ofReal.comp (hc ν t hν Ψ hΨ i s hs)).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hb z).trans (mul_le_mul_of_nonneg_right
      (le_abs_self C) (Real.exp_pos _).le)) (norm_nonneg _)
  · obtain ⟨ε, hε, hεs, C, R, a, ha, hb⟩ := h2 ν t hν ht Ψ hΨ i s hs
    refine ⟨ε, hε, hεs, fun z => ‖g z i‖ * (|C| * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2)), ?_, ?_⟩
    · have := (hG c r hc0 hr g hg i R a ha).mul_const |C|
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [mul_assoc, mul_comm |C|]
    · intro s' hs' z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hb s' hs' z).trans (mul_le_mul_of_nonneg_right
        (le_abs_self C) (Real.exp_pos _).le)) (norm_nonneg _)

end UnforcedLeray.Short.IIb
