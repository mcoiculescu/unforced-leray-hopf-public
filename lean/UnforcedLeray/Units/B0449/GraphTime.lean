import UnforcedLeray.Units.B0449.GraphChart
import UnforcedLeray.Units.B0447.Chart

/-!
# B0449 graph time identity for a joint representative

The Bochner weak time derivative of the B0447 chart is projected by a spatial test functional,
then passed to the non-product space-time test theorem in `TimeST`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.BochnerTime

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The chart weak time identity, tested against a fixed spatial component functional, holds for
its jointly measurable representatives and arbitrary compactly supported space-time tests. -/
theorem chartJ_timeDerivative {ν : ℝ} (hν : 0 < ν) (hq : q ≠ ⊤) {w b : Yq P q}
    (h : HasPhaseOp driftT w b) (τ₀ : ℝ) (e : CVec3)
    {a₀ b₀ : ℝ}
    {θ θt : ℝ × Space → ℂ} (hθ : Continuous θ) (hθt : Continuous θt)
    (hd : ∀ t z, HasDerivAt (fun s => θ (s, z)) (θt (t, z)) t)
    {a' b' M R : ℝ} (ha : a₀ < a') (hab' : a' ≤ b') (hb : b' < b₀) (hM : 0 ≤ M)
    (hθb : ∀ t z, ‖θ (t, z)‖ ≤
      M * (Icc a' b').indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hθtb : ∀ t z, ‖θt (t, z)‖ ≤
      M * (Icc a' b').indicator (fun _ => (1 : ℝ)) t * ballInd R z) :
    ∫ p, θt p * dotL e (chartJ w ν τ₀ p) =
      -∫ p, θ p * dotL e (chartJ b ν τ₀ p) := by
  let L0 : CVec3 →L[ℝ] ℂ := (dotL e).restrictScalars ℝ
  let L : Lp CVec3 q (volume : Measure Space) →L[ℝ]
      Lp ℂ q (volume : Measure Space) := L0.compLpL q volume
  let u : ℝ → Lp ℂ q (volume : Measure Space) := fun t =>
    L (B0447.chartLp w ν τ₀ 0 t)
  let v : ℝ → Lp ℂ q (volume : Measure Space) := fun t =>
    L (B0447.chartLp b ν τ₀ 0 t)
  let U : ℝ × Space → ℂ := fun p => dotL e (chartJ w ν τ₀ p)
  let Ut : ℝ × Space → ℂ := fun p => dotL e (chartJ b ν τ₀ p)
  have hweakChart := B0447.chart_hasWeakDerivTime hq h ν τ₀ 0 a₀ b₀
  have hweakScalar : HasWeakDerivTime a₀ b₀ u v := by
    simpa [u, v, L] using hweakChart.map L
  have hU : StronglyMeasurable U := by
    dsimp [U]
    exact (dotL e).continuous.comp_stronglyMeasurable (stronglyMeasurable_chartJ w ν τ₀)
  have hUt : StronglyMeasurable Ut := by
    dsimp [Ut]
    exact (dotL e).continuous.comp_stronglyMeasurable (stronglyMeasurable_chartJ b ν τ₀)
  have hUslice : ∀ t ∈ Ioo a₀ b₀, (fun z => U (t, z)) =ᵐ[volume] u t := by
    intro t ht
    have hJ := chartJ_slice_lp hν w τ₀ t
    have hmap := L0.coeFn_compLpL (B0447.chartLp w ν τ₀ 0 t)
    have hslice : (fun z => U (t, z)) =ᵐ[volume]
        (fun z => L0 ((B0447.chartLp w ν τ₀ 0 t : Space → CVec3) z)) := by
      filter_upwards [hJ] with z hz
      change dotL e (chartJ w ν τ₀ (t, z)) = _
      rw [hz]
      rfl
    simpa [U, u, L, L0] using hslice.trans hmap.symm
  have hUtslice : ∀ t ∈ Ioo a₀ b₀, (fun z => Ut (t, z)) =ᵐ[volume] v t := by
    intro t ht
    have hJ := chartJ_slice_lp hν b τ₀ t
    have hmap := L0.coeFn_compLpL (B0447.chartLp b ν τ₀ 0 t)
    have hslice : (fun z => Ut (t, z)) =ᵐ[volume]
        (fun z => L0 ((B0447.chartLp b ν τ₀ 0 t : Space → CVec3) z)) := by
      filter_upwards [hJ] with z hz
      change dotL e (chartJ b ν τ₀ (t, z)) = _
      rw [hz]
      rfl
    simpa [Ut, v, L, L0] using hslice.trans hmap.symm
  exact integral_dt_mul_eq hweakScalar hU hUt hUslice hUtslice hθ hθt hd
    ha hab' hb hM hθb hθtb

end UnforcedLeray.B0449
