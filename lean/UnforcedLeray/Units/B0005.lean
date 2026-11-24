import UnforcedLeray.Units.B0005.Similarity
import UnforcedLeray.Units.B0005.Spaces
import UnforcedLeray.Units.B0005.Unique
import UnforcedLeray.Units.B0005.Bridge
import UnforcedLeray.Units.B0005.Consistency

/-!
# Unit B0005 (`unlabeled:136`): similarity variables and the periodic graph spaces

Blueprint unit `B0005`, `paper/main.tex` lines 136–147:

> In similarity variables `y = x/√t`, `τ = log t`, for a period `𝒯 > 0`, set
> `𝒴_q = L^q([0,𝒯], dτ/𝒯; L^q)`, `𝒯₀ = ∂_τ - ½ y·∇`,
> `𝒱_q = {f ∈ 𝒴_{q,div} : hΔf, 𝒯₀f ∈ 𝒴_q}`.
> The periodic spaces identify their endpoints; the graph norm is the sum of the three
> indicated norms. No separate phase derivative or dilation derivative is imposed.

Consumers (blueprint `depends_on`): B0440 (`eq:m3-free-graph`, the inverse on `𝒱_q`), B1007
(`loc:eq:graph`, `loc:eq:mode`), B1009, B1033, B1034 (`prop:unstable-background`). Only
`q = 2` is used downstream.

## Definitions (namespace `UnforcedLeray.B0005`)

| Manuscript | Lean | File |
|---|---|---|
| `y = x/√t`, `τ = log t` | `simY`, `simTau`, `toSimilarity` (inverse `fromSimilarity`) | `B0005/Similarity` |
| `𝒴_q` (endpoints identified) | `Y 𝒯 q = PhaseSpace.Yq 𝒯 q` on `AddCircle 𝒯`, `phase` | `B0005/Spaces` |
| `dτ/𝒯` | `AddCircle.haarAddCircle` (`measurePreserving_phase`, `norm_rpow_eq`) | `B0005/Spaces` |
| `𝒴_{q,div}` | `Ydiv 𝒯 q` | `B0005/Spaces` |
| `𝒯₀` | `T0op` on smooth functions, `HasT0` in distributions (transpose `driftT`) | `B0005/Spaces` |
| `hΔf ∈ 𝒴_q` in distributions | `HasHLap h` (transpose `nuLapT h`) | `B0005/Spaces` |
| `𝒱_q` as the graph `{(f, hΔf, 𝒯₀f)}` | `V 𝒯 q h = PhaseSpace.solenoidalFreeGraph 𝒯 h q` | `B0005/Spaces` |
| `𝒱_q ⊂ 𝒴_q`, graph norm `‖f‖+‖hΔf‖+‖𝒯₀f‖` | `Vq`, `hLapOf`, `T0Of`, `graphNormV`, `graphEquiv` | `B0005/Unique` |


Bochner model and the periodic tests; this file follows it. The scalars are complex (tex 7314);
real fields are handled in the bridge below.

## Asserted facts

* `B0005.facts`: similarity variables are a bijection of `(0,∞) × ℝ³` onto `ℝ × ℝ³`; `0` and
  `𝒯` are the same phase; the phase measure is `dτ/𝒯`; `𝒴_{q,div}` and `𝒱_q` are closed (so
  `𝒱_q` with the graph norm is a Banach space, `graphNormV_equiv`); and the graph triple is
  determined by `f` (phase tests separate `𝒴_q`, `eq_zero_of_phasePair`), so the graph norm is a
  function of `f`.
* "No separate phase or dilation derivative": `mem_V_iff` lists the only conditions; the
  distributional `𝒯₀` is tested through `driftT` (`driftT_eq_neg_T0op`), never through `∂_τ` or
  `y·∇` separately.
* The distributional operators extend the classical ones (`B0005/Consistency`): for a smooth
  `𝒯`-periodic `Φ` of bounded support, `hasT0_testElem` (`𝒯₀Φ = ∂_τΦ - ½ y·∇Φ` in
  distributions) and `hasHLap_testElem` (`hΔΦ` in distributions), so `driftT` and `nuLapT h` are
  the transposes of `𝒯₀` and `hΔ`.

## Agreement with the interface layer (`Blueprint/Package.lean`, `Blueprint/Localization/Spaces.lean`)

* `heatProfile_eq_profile`, `simY_eq_rpow`: `Blueprint.heatProfile` and
  `Blueprint.physicalDilation` use these similarity variables.
* `isY2Div_iff`: `Blueprint.IsY2Div 𝒯 f ↔ IsY2 𝒯 f ∧ toY 𝒯 f ∈ Ydiv 𝒯 2`.
* `inPeriodicGraph_iff`: for `h ≠ 0`, `Blueprint.InPeriodicGraph 𝒯 b a d` iff the three real
  fields are `IsY2` and `(toY b, h · toY a, toY d) ∈ V 𝒯 2 h`.
* `IsY2.norm_toY_sq`, `IsY2.toY_eq_zero_iff`: the norm of `𝒴₂` is the interface's slab norm
  with weight `1/𝒯`.

Status: every declaration here is proved (no hypotheses beyond the manuscript's). This is a
definition unit; Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace

/-- **Unit B0005, asserted facts** (tex 136–147), for a period `𝒯 > 0`, an exponent `q ≥ 1`
and a viscosity `h`:
1. `(t, x) ↦ (log t, x/√t)` is a bijection of `(0, ∞) × ℝ³` onto `ℝ × ℝ³`;
2. the endpoints `0` and `𝒯` of the phase interval are identified;
3. the phase measure is `dτ/𝒯` on one period;
4. `𝒴_{q,div}` is closed in `𝒴_q`;
5. `𝒱_q` is closed in `𝒴_q³`, hence complete for the graph norm;
6. an element of `𝒱_q` is determined by `f`: `hΔf` and `𝒯₀f` are unique. -/
theorem facts (𝒯 : ℝ) [Fact (0 < 𝒯)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℝ) :
    BijOn toSimilarity (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) univ ∧
      phase 𝒯 0 = phase 𝒯 𝒯 ∧
      MeasurePreserving (phase 𝒯) ((ENNReal.ofReal 𝒯)⁻¹ • volume.restrict (Ioc (0 : ℝ) 𝒯))
        (AddCircle.haarAddCircle (T := 𝒯)) ∧
      IsClosed (Ydiv 𝒯 q : Set (Y 𝒯 q)) ∧
      IsClosed (V 𝒯 q h : Set (Y 𝒯 q × Y 𝒯 q × Y 𝒯 q)) ∧
      (∀ x y : Y 𝒯 q × Y 𝒯 q × Y 𝒯 q, x ∈ V 𝒯 q h → y ∈ V 𝒯 q h → x.1 = y.1 → x = y) :=
  ⟨bijOn_toSimilarity, phase_zero_eq_phase_period 𝒯, measurePreserving_phase 𝒯,
    isClosed_Ydiv 𝒯 q, isClosed_V h, fun _ _ hx hy hxy => V_ext hx hy hxy⟩

end UnforcedLeray.B0005
