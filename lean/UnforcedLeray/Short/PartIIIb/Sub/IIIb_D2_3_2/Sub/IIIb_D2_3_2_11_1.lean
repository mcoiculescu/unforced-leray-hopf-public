import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs

/-!
# Decomposition of `StrSmoothDense` (`PartIII-b:IIIb-D2/3/2/11/1`, source 4284-4286, 2666-2700)

`strSmoothDense_of`: `StrSmoothDense` follows from (i) the generic `Lp` density of smooth chart
tensors for measures finite on compacts and null off `chartDom c` (`LpSmoothDense`), and (ii) the
two measure facts for the gain-weighted chart measures (`GainMeasuresOK`).  The product step
(`StrG = WithLp 1 (Lp × Lp)`) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(i) Generic density** (source 4284-4286): for `c > 0` and a measure `μ` on the chart that is
finite on compacts and gives measure zero to the complement of the open chart domain `chartDom c`,
the `L²(μ; Ten3)` classes with a smooth compactly supported representative inside `chartDom c` are
dense.  (Proof: `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`
(`Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`) gives smooth compactly supported approximants on
`Chart`; multiply by smooth cutoffs `ψₙ` with compact support inside `chartDom c`, `0 ≤ ψₙ ≤ 1`,
`ψₙ → 1` on `chartDom c`, and pass to the limit by dominated convergence.) -/
def LpSmoothDense : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ μ : Measure Chart, IsFiniteMeasureOnCompacts μ → μ (chartDom c)ᶜ = 0 →
    Dense {f : Lp (α := Chart) Ten3 2 μ | ∃ G : Chart → Ten3, f =ᵐ[μ] G ∧ IsSmoothChart c G}

/-- **(ii) The gain-weighted chart measures** (source 2697-2700, 2666-2689): for `c, ν > 0` the
measures `gainZ1Measure c mZ γ ν = g⁻²W² s^{-1/2} dς` and `gainHTMeasure c ρb γ ν =
g⁻²ρ_b⁻¹ s^{-1/2} dς` are finite on compacts of `Chart` (densities locally bounded on `s ≥ 0`,
`s^{-1/2}` integrable at `0`; for `ρb ≤ 0` the second is `0`) and are carried by `(0,∞) × [-c/2,c/2)
× ℝ`, so give measure `0` to `(chartDom c)ᶜ` (the seam `q = -c/2` is null). -/
def GainMeasuresOK : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < c → 0 < ν →
    IsFiniteMeasureOnCompacts (gainZ1Measure c mZ γ ν) ∧
    IsFiniteMeasureOnCompacts (gainHTMeasure c ρb γ ν) ∧
    gainZ1Measure c mZ γ ν (chartDom c)ᶜ = 0 ∧
    gainHTMeasure c ρb γ ν (chartDom c)ᶜ = 0

theorem strSmoothDense_of (h1 : LpSmoothDense) (h2 : GainMeasuresOK) (c mZ ρb γ ν : ℝ) :
    StrSmoothDense c mZ ρb γ ν := by
  intro hc hν
  obtain ⟨a1, a2, a3, a4⟩ := h2 c mZ ρb γ ν hc hν
  haveI := a1
  haveI := a2
  have d1 := h1 c hc _ a1 a3
  have d2 := h1 c hc _ a2 a4
  have hprod := d1.prod d2
  let e := WithLp.prodContinuousLinearEquiv (p := 1) (𝕜 := ℝ)
    (α := Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (β := Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
  have hd := hprod.preimage e.toHomeomorph.isOpenMap
  refine hd.mono ?_
  intro T hT
  obtain ⟨⟨G₁, hG₁, hs₁⟩, ⟨G₂, hG₂, hs₂⟩⟩ := hT
  exact ⟨G₁, G₂, hG₁, hG₂, hs₁, hs₂⟩

end UnforcedLeray.Short.PartIIIb.Concrete
