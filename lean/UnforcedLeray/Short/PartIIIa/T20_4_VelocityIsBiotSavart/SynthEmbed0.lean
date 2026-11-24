import UnforcedLeray.Short.PartIIIa.Sub.T20_4

/-!
# Part III-a, task `PartIII-a:T20/4/4`: synthesis commutes with `z ↦ z e₀`

Proves `CTE.SynthEmbed0` (statement in `Sub/T20_4.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3240 (the mode series of
`K_c ω` is the series of the `ℂ²`-valued mode fields).

Proof. `B0581.synth c g = ∑ₖ tensorLI c k (g k)` (`hasSum_synth`), `embed0Lp c` is continuous, and
`embed0Lp c (tensorLI c k a) = tensorLI c k (a e₀)` pointwise (`coeFn_tensorLM`,
`coeFn_compLpL`, `tensorFun_ae_congr`, `map_smul`); uniqueness of the sum of the `ℂ²`-valued
series `hasSum_synth c (embed0Modes g)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.IIIa

namespace CTE

theorem embed0Lp_tensorLI (c : ℝ) [Fact (0 < c)] (k : ℤ) (a : Lp ℂ 2 (volume : Measure ℝ)) :
    embed0Lp c (B0581.tensorLI c k a) =
      B0581.tensorLI c k (ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a) := by
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL embed0 (B0581.tensorLI c k a),
    B0581.coeFn_tensorLM c k a,
    B0581.coeFn_tensorLM c k (ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a),
    B0581.tensorFun_ae_congr c k (ContinuousLinearMap.coeFn_compLpL embed0 a)] with x h1 h2 h3 h4
  have h1' : (embed0Lp c (B0581.tensorLI c k a) : B0579.Plane → B0581.Vel) x =
      embed0 ((B0581.tensorLI c k a : B0579.Plane → ℂ) x) := h1
  have h2' : (B0581.tensorLI c k a : B0579.Plane → ℂ) x = B0581.tensorFun c k a x := h2
  have h3' : (B0581.tensorLI c k (ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a) :
      B0579.Plane → B0581.Vel) x =
      B0581.tensorFun c k (ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a) x := h3
  rw [h1', h2', h3', h4]
  simp only [B0581.tensorFun, map_smul]

theorem synthEmbed0 : SynthEmbed0 := by
  intro c hc g
  have h2 := (B0581.hasSum_synth c g).mapL (embed0Lp c)
  have h3 := B0581.hasSum_synth c (embed0Modes g)
  refine h2.unique ?_
  simp only [embed0Lp_tensorLI]
  exact h3

end CTE

end UnforcedLeray.Short.IIIa
