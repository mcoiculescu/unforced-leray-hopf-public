import UnforcedLeray.Short.PartIIb.Sub.T12_7

/-!
# Part II-b, task `PartII-b:T12/7/4` (`DeqHeatPair`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the heat flow
`e^{ν(s-t)Δ}` tends to the identity as `s → t+`).

`deqHeatPair_of` proves `DeqHeatPair` by dominated convergence along `𝓝[>] t` from four leaf Props:
continuity of the smoothed test, uniform convergence to `Ψ(t, ·)`, a Gaussian envelope, and the
integrability of a Gaussian envelope against a periodic `L^r` slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- For `s > t` the smoothed test `z ↦ deqSmooth ν Ψ i t s z` is continuous (convolution of the
continuous compactly supported `Ψ_i(s, ·)` with an integrable kernel). SP 1923-1927. -/
def DeqhpCont : Prop :=
  ∀ (ν t : ℝ), 0 < ν → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2, ∀ s : ℝ, t < s →
    Continuous (deqSmooth ν Ψ i t s)

/-- Uniform approximate identity: `deqSmooth ν Ψ i t s → Ψ(t, ·)_i` uniformly on the plane as
`s → t+` (uniform continuity and compact support of `Ψ_i`, kernel of mass 1 concentrating at 0).
SP 1923-1927. -/
def DeqhpUnif : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2,
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, t < s → s < t + δ → ∀ z : ℝ × ℝ,
      |deqSmooth ν Ψ i t s z - Ψ (t, z) i| ≤ ε

/-- Gaussian envelope uniform in `s ∈ (t, t+1]`: if `Ψ_i(s, ·)` is supported in a fixed ball of
radius `R₀` and bounded, then `|U(s, z)| ≤ C e^{-a (‖z‖ - R)_+²}` with `a, R` depending on `ν` and
`R₀` (Gaussian tail of the heat kernel of age `ν(s-t) ≤ ν`). SP 1923-1927. -/
def DeqhpTail : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2,
    ∃ C R a : ℝ, 0 < a ∧ ∀ s : ℝ, t < s → s ≤ t + 1 → ∀ z : ℝ × ℝ,
      |deqSmooth ν Ψ i t s z| ≤ C * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2)

/-- A periodic `L^r` slice (`r > 1`) is uniformly `L^1` on unit boxes, hence integrable against
any Gaussian envelope. SP 1923-1927. -/
def DeqhpGaussInt : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g → ∀ (i : Fin 2) (R a : ℝ),
    0 < a → Integrable (fun z : ℝ × ℝ => ‖g z i‖ * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2))

theorem deqHeatPair_of (h1 : DeqhpCont) (h2 : DeqhpUnif) (h3 : DeqhpTail) (h4 : DeqhpGaussInt) :
    DeqHeatPair := by
  intro ν c r t hν ht hc hr g hg Ψ hΨ i
  obtain ⟨C, R, a, ha, hbd⟩ := h3 ν t hν ht Ψ hΨ i
  have hint := h4 c r hc hr g hg i R a ha
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖g z i‖ * (|C| * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2))) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : t < s := hs
    have hgi : AEStronglyMeasurable (fun z => g z i) volume :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hg.2.1
    exact hgi.mul (Complex.continuous_ofReal.comp (h1 ν t hν Ψ hΨ i s hs')).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show t < t + 1 by linarith)] with s hs
    refine Eventually.of_forall fun z => ?_
    have := hbd s hs.1 hs.2 z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)) (norm_nonneg _)
  · have := hint.const_mul |C|
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]; ring
  · refine Eventually.of_forall fun z => ?_
    refine Tendsto.const_mul (g z i) ?_
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hs⟩ := h2 ν t hν ht Ψ hΨ i (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun s hs1 hs2 => ?_⟩
    have hs1' : t < s := hs1
    have hs2' : s < t + δ := by
      have := (Real.dist_eq s t) ▸ hs2; have := abs_lt.mp this; linarith
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := hs s hs1' hs2' z
    linarith
