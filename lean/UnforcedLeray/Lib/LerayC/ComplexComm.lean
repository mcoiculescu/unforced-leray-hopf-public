import UnforcedLeray.Lib.LerayC.Complex

/-!
# The complex `L^p` Leray projection: real fields, consistency, translations, heat (INF01 T17)

Blueprint: INF01 target T17 (`ℂ³` version) together with the T16 commutations for complex

LERAY-C. Manuscript: unit B0414 (`paper/main.tex` lines 7336–7344: `P_σ` on `L^q(R³;ℂ³)`
commutes with the heat semigroup), unit B0430 (lines 3720–3732: the operators at different
exponents agree on the intersections).

* `compLpL_compLpL`, `compLpL_spaceTranslateLp`: composition with pointwise linear maps;
* `lerayC_ofRe`: on real fields `lerayC` is `lerayLp`;
* `lerayC_consistent`: for `F ∈ L^p ∩ L^q(R³;ℂ³)` the two projections agree a.e.;
* `lerayC_translate`, `lerayC_heat`: `𝔓 τ_y = τ_y 𝔓` and `𝔓 e^{θΔ} = e^{θΔ} 𝔓` on
  `L^p(R³;ℂ³)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

open UnforcedLeray.PhaseSpace (CVec3)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

section General

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compLpL_compLpL (L : F →L[ℝ] G) (M : E →L[ℝ] F) (u : Lp E p (volume : Measure Space)) :
    L.compLpL p volume (M.compLpL p volume u) = (L.comp M).compLpL p volume u := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (μ := volume) (p := p) (M.compLpL p volume u),
    M.coeFn_compLpL (μ := volume) (p := p) u,
    (L.comp M).coeFn_compLpL (μ := volume) (p := p) u] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

theorem compLpL_toLp (L : E →L[ℝ] F) {f : Space → E} (hf : MemLp f p volume) :
    L.compLpL p volume (hf.toLp f) = (L.comp_memLp' hf).toLp (⇑L ∘ f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (μ := volume) (p := p) (hf.toLp f), hf.coeFn_toLp,
    (L.comp_memLp' hf).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

variable [CompleteSpace E] [CompleteSpace F]

theorem spaceTranslateLp_add (y : Space) (u v : Lp E p (volume : Measure Space)) :
    spaceTranslateLp p y (u + v) = spaceTranslateLp p y u + spaceTranslateLp p y v :=
  map_add (Lp.compMeasurePreserving _ _) u v

/-- Pointwise linear maps commute with translations. -/
theorem compLpL_spaceTranslateLp (L : E →L[ℝ] F) (y : Space)
    (u : Lp E p (volume : Measure Space)) :
    L.compLpL p volume (spaceTranslateLp p y u) = spaceTranslateLp p y (L.compLpL p volume u) := by
  apply Lp.ext
  have h1 := L.coeFn_compLpL (μ := volume) (p := p) (spaceTranslateLp p y u)
  have h2 := coeFn_spaceTranslateLp (p := p) y u
  have h3 := coeFn_spaceTranslateLp (p := p) y (L.compLpL p volume u)
  have h4 := ae_eq_comp_sub (L.coeFn_compLpL (μ := volume) (p := p) u) y
  refine h1.trans (EventuallyEq.trans ?_ (h3.trans h4).symm)
  filter_upwards [h2] with x hx
  rw [hx]

end General

/-- On real fields, the complex Leray projection is the real one:
`𝔓(ι G) = ι(𝔓 G)` for `ι = ofReV : R³ → ℂ³`. -/
theorem lerayC_ofRe (hp1 : 1 < p) (hp : p ≠ ⊤) (G : Lp Space p (volume : Measure Space)) :
    lerayC p hp1 hp (ofReV.compLpL p volume G) = ofReV.compLpL p volume (lerayLp p hp1 hp G) := by
  have e1 : reV.compLpL p volume (ofReV.compLpL p volume G) = G := by
    rw [compLpL_compLpL]
    apply Lp.ext
    filter_upwards [(reV.comp ofReV).coeFn_compLpL (μ := volume) (p := p) G] with x hx
    rw [hx, ContinuousLinearMap.comp_apply, reV_ofReV]
  have e2 : imV.compLpL p volume (ofReV.compLpL p volume G) = 0 := by
    rw [compLpL_compLpL]
    apply Lp.ext
    filter_upwards [(imV.comp ofReV).coeFn_compLpL (μ := volume) (p := p) G,
      Lp.coeFn_zero Space p (volume : Measure Space)] with x hx h0
    rw [hx, h0, ContinuousLinearMap.comp_apply, imV_ofReV]
    rfl
  rw [lerayC_apply, e1, e2, map_zero, map_zero, add_zero]

/-- **Consistency across exponents (B0430, `paper/main.tex` lines 3720–3732).** For
`F ∈ L^p ∩ L^q(R³;ℂ³)`, `1 < p, q < ∞`, the complex Leray projections at `p` and at `q` agree
a.e. -/
theorem lerayC_consistent {q : ℝ≥0∞} [Fact (1 ≤ q)] (hp1 : 1 < p) (hp : p ≠ ⊤) (hq1 : 1 < q)
    (hq : q ≠ ⊤) {F : Space → CVec3} (hFp : MemLp F p volume) (hFq : MemLp F q volume) :
    (lerayC p hp1 hp (hFp.toLp F) : Space → CVec3) =ᵐ[volume] lerayC q hq1 hq (hFq.toLp F) := by
  have hre := lerayLp_consistent hp1 hp hq1 hq (reV.comp_memLp' hFp) (reV.comp_memLp' hFq)
  have him := lerayLp_consistent hp1 hp hq1 hq (imV.comp_memLp' hFp) (imV.comp_memLp' hFq)
  filter_upwards [coeFn_lerayC hp1 hp (hFp.toLp F), coeFn_lerayC hq1 hq (hFq.toLp F), hre, him]
    with x h1 h2 h3 h4
  rw [h1, h2, compLpL_toLp, compLpL_toLp, compLpL_toLp, compLpL_toLp, h3, h4]

/-- **INF01 T16 for `ℂ³` (translations).** `𝔓 τ_y = τ_y 𝔓` on `L^p(R³;ℂ³)`, `1 < p < ∞`. -/
theorem lerayC_translate (hp1 : 1 < p) (hp : p ≠ ⊤) (y : Space)
    (F : Lp CVec3 p (volume : Measure Space)) :
    lerayC p hp1 hp (spaceTranslateLp p y F) = spaceTranslateLp p y (lerayC p hp1 hp F) := by
  rw [lerayC_apply, lerayC_apply, compLpL_spaceTranslateLp, compLpL_spaceTranslateLp,
    lerayLp_translate, lerayLp_translate, compLpL_spaceTranslateLp, compLpL_spaceTranslateLp,
    spaceTranslateLp_add]

/-- **INF01 T16 for `ℂ³` (heat semigroup).** For `1 < p < ∞` and every heat time `θ`, the complex
Leray projection commutes with `e^{θΔ}` on `L^p(R³;ℂ³)` (B0414 (iv), `paper/main.tex`
lines 7343–7344). -/
theorem lerayC_heat (hp1 : 1 < p) (hp : p ≠ ⊤) (θ : ℝ) :
    ((lerayC p hp1 hp).restrictScalars ℝ).comp
        (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ) =
      (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ).comp
        ((lerayC p hp1 hp).restrictScalars ℝ) :=
  Heat.heatLp_comm (AddMonoidHom.id Space) continuous_id hp
    (fun y u => lerayC_translate hp1 hp y u) θ

end UnforcedLeray.RieszLp
