import UnforcedLeray.Lib.HeatR3.Line
import UnforcedLeray.Lib.HeatR3.LpOp

/-!
# The line heat flow is the generic heat operator (INF04 BP1 on `ℝ`, INF05 T18)


the 1D heat flow `lineHeat` (T18) is `heatConv lineι` with `lineι : ℝ¹ →+ ℝ`, `y ↦ y₀`, so the
generic results of `ConvOp`/`LpOp` (contraction on `L^p(ℝ)`, semigroup law, `heatLp` on
`L^p(ℝ)`) apply to it (B0158, tex 2394–2404).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The coordinate homomorphism `ℝ¹ → ℝ`, `y ↦ y₀`. -/
def lineι : Euc 1 →+ ℝ := (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).toLinearMap.toAddMonoidHom

theorem lineι_apply (y : Euc 1) : lineι y = y 0 := rfl

theorem continuous_lineι : Continuous lineι :=
  (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).continuous

/-- **BP1 on the line.** `lineHeat θ f = heatConv lineι θ f` for every `θ` and `f`. -/
theorem lineHeat_eq_heatConv (θ : ℝ) (f : ℝ → ℝ) : lineHeat θ f = heatConv lineι θ f := by
  funext η
  simp only [lineHeat, heatConv]
  rw [← measurePreserving_lineIso.integral_comp lineIso.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [LinearIsometryEquiv.coe_toHomeomorph, lineι_apply, lineIso_apply, lineGauss_eq,
    smul_eq_mul]

/-- The heat semigroup law on the line, from the generic one: for `f ∈ L^p(ℝ)`, `1 ≤ p ≤ ∞`,
`e^{(s+t)∂²}f = e^{s∂²}e^{t∂²}f` a.e. -/
theorem lineHeat_add_time {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : MemLp f p volume) :
    lineHeat (s + t) f =ᵐ[volume] lineHeat s (lineHeat t f) := by
  simp only [lineHeat_eq_heatConv]
  exact heatConv_add_time lineι continuous_lineι.measurable hs ht hp hf

end UnforcedLeray.Heat
