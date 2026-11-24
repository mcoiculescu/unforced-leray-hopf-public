import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Short.Interface.Leaf2_Integrability.Pairings
import UnforcedLeray.Short.Interface.Leaf2_Integrability.CouplingIntegrable

/-!
# Interface leaf 2 (task `Interface:I10`): the integrability clauses of the weak mode equation

Proves `ModeSolutionIntegrability` (`Statements.lean`, helper 2b-5, source lines 176-187 and
6086-6150 of `the November 2 reference manuscript`): for a regular background `V`
(`IsL3Background`) and a periodic `H¹` mode `b` (`IsH1Periodic`), every pairing of the mode
equation with a similarity test is integrable:

* `pairTerm`, `temporalTerm`, `dilationTerm`, `diffusionTerm` of `b` (`Leaf2_Integrability/Pairings`):
  each is the pairing of `b` with a smooth phase test of bounded time window (`ψ`, `∂_τψ`,
  `(y·∇)ψ`, `Δψ`), integrable by the library unfolding `B0005.IsY2.pairTerm_unfold`;
* the columns `symTensorColumns (V τ) (b τ)` are `L²` at almost every phase, so each
  `lerayDivIntegrand` is integrable (`lerayDivIntegrand_integrable`);
* the coupling `τ ↦ weakCoupling V b ψ τ` is integrable (`Leaf2_Integrability/CouplingIntegrable`,
  Fubini representatives of the projected test slices, `L²` bound, periodicity of `b`).

No hypothesis is added; the proof uses only the library and the helper files.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- **Helper 2b-5**: the integrability fields of `IsWeakModeSolution` for a periodic `H¹` field on
a regular background. -/
theorem modeSolutionIntegrability : ModeSolutionIntegrability := by
  intro P V dV b hP hV hb ψ hψ
  obtain ⟨C, hC⟩ := hV.bounded
  obtain ⟨h1, h2, h3, h4⟩ :=
    Leaf2_Integrability.pairTerms_integrable hP hb.value.isY2 hψ
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · have hcol : ∀ᵐ τ : ℝ, ColumnsL2 (symTensorColumns (V τ) (b τ)) :=
      (ModeId.Y2.ae_memLp hP hb.value).mono fun τ hτ =>
        columnsL2_symTensor (hV.continuous τ) (hC τ) hτ
    filter_upwards [hcol] with τ hτ
    exact fun j => lerayDivIntegrand_integrable hτ (Blueprint.slice ψ τ) j
  · exact Leaf2_Integrability.integrable_weakCoupling hP hV.continuous hC hV.measurable
      hb.value hψ

end UnforcedLeray.Short.Interface
