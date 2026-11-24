import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Sub.T12_7_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7

/-!
# Part II-b, task `PartII-b:T12/7/5` (`dfe_DeqPairDeriv`): decomposition

Source: `the November 2 reference manuscript`,
lines 1923-1927 (the `s`-derivative of the heat-smoothed pairing).

`dfe_DeqPairDeriv` follows from three Props by differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):

* `dfe_DeqPdPointwise`: for each fixed `z`, `s ↦ deqSmooth ν Ψ i t s z` has derivative `deqSmoothD`
  (derivative under the `w`-integral, heat equation via `DeqHeatDeriv`);
* `dfe_DeqPdCont`: for each `s > t`, `deqSmooth ν Ψ i t s` and `deqSmoothD ν Ψ i t s` are continuous in
  `z` (measurability for the outer integral);
* `dfe_DeqPdDominate`: local domination of `g_i * deqSmoothD` by an integrable function near `s`
  (Gaussian tails outside the support box, periodic `L^r` slice integrable on unit boxes).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Lemma 1** (SP 1923-1927): pointwise `s`-derivative of the heat-smoothed test,
`d/ds ∫ K_{ν(s-t)}(w) Ψ_i(s, z-w) dw = ∫ K_{ν(s-t)}(w) [∂_sΨ_i + νΔΨ_i](s, z-w) dw`.
Proof: differentiate under the `w`-integral (local majorant
`abs_heatKernel2AgeDerivative_le_local` of `Lib/HeatCylinder/HeatKernelAgeMajorant.lean`,
`flatHeat_kernel_eq` of `Tasks/FlatCausal/FlatHeatContraction.lean`), then `deqHeatDeriv` moves
`Δ` from the kernel onto `Ψ_i(s, z - ·)`. -/
def dfe_DeqPdPointwise : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarTestDfe Ψ → ∀ i : Fin 2,
    ∀ s : ℝ, t < s → ∀ z : ℝ × ℝ,
      HasDerivAt (fun s' : ℝ => deqSmooth ν Ψ i t s' z) (deqSmoothD ν Ψ i t s z) s

/-- **Lemma 2** (SP 1923-1927): continuity in `z` of the smoothed tests (convolution of the
Gaussian with a compactly supported smooth function). -/
def dfe_DeqPdCont : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarTestDfe Ψ → ∀ i : Fin 2,
    ∀ s : ℝ, t < s →
      Continuous (fun z : ℝ × ℝ => deqSmooth ν Ψ i t s z) ∧
        Continuous (fun z : ℝ × ℝ => deqSmoothD ν Ψ i t s z)

/-- **Lemma 3** (SP 1923-1927): local domination. `|deqSmoothD(s', z)| ≤ C exp(-d(z,B)²/(8θ_max))`
for `s'` near `s` (support box `B` of `Ψ`), and a `DeqSliceGood` slice is uniformly `L^1` on unit
boxes (Hölder + periodic unfolding; `Tasks/FlatUnique/CellStream/HrBox.lean`,
`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`), so the product is integrable. -/
def dfe_DeqPdDominate : Prop :=
  ∀ (ν c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarTestDfe Ψ → ∀ i : Fin 2, ∀ s : ℝ, t < s →
        Integrable (fun z : ℝ × ℝ => g z i * (deqSmooth ν Ψ i t s z : ℂ)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < s - t ∧ ∃ bound : ℝ × ℝ → ℝ, Integrable bound ∧
          ∀ s' ∈ Metric.ball s ε, ∀ z : ℝ × ℝ,
            ‖g z i * (deqSmoothD ν Ψ i t s' z : ℂ)‖ ≤ bound z

theorem dfe_deqPairDeriv_of (h1 : dfe_DeqPdPointwise) (h2 : dfe_DeqPdCont) (h3 : dfe_DeqPdDominate) :
    dfe_DeqPairDeriv := by
  intro ν c r t hν ht hc hr g hg Ψ hΨ i s hs
  obtain ⟨hint, ε, hε, hεs, bound, hbi, hb⟩ := h3 ν c r t hν ht hc hr g hg Ψ hΨ i s hs
  have hgi : AEStronglyMeasurable (fun z : ℝ × ℝ => g z i) volume :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable hg.2.1
  have hmeas : ∀ s' : ℝ, t < s' →
      AEStronglyMeasurable (fun z : ℝ × ℝ => g z i * (deqSmooth ν Ψ i t s' z : ℂ)) volume := by
    intro s' hs'
    exact hgi.mul ((Complex.continuous_ofReal.comp (h2 ν t hν ht Ψ hΨ i s' hs').1).aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable
      (fun z : ℝ × ℝ => g z i * (deqSmoothD ν Ψ i t s z : ℂ)) volume :=
    hgi.mul ((Complex.continuous_ofReal.comp (h2 ν t hν ht Ψ hΨ i s hs).2).aestronglyMeasurable)
  have hgt : ∀ s' ∈ Metric.ball s ε, t < s' := by
    intro s' hs'
    have h := Metric.mem_ball.mp hs'
    rw [Real.dist_eq] at h
    have := (abs_lt.mp h).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun (s' : ℝ) (z : ℝ × ℝ) => g z i * (deqSmooth ν Ψ i t s' z : ℂ))
    (F' := fun (s' : ℝ) (z : ℝ × ℝ) => g z i * (deqSmoothD ν Ψ i t s' z : ℂ))
    (x₀ := s) (bound := bound) (Metric.ball_mem_nhds s hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds s hε) (fun s' hs' => hmeas s' (hgt s' hs')))
    hint hmeas' (Filter.Eventually.of_forall (fun z s' hs' => hb s' hs' z)) hbi
    (Filter.Eventually.of_forall (fun z s' hs' =>
      ((h1 ν t hν ht Ψ hΨ i s' (hgt s' hs') z).ofReal_comp).const_mul (g z i)))
  exact key.2

end UnforcedLeray.Short.IIb
