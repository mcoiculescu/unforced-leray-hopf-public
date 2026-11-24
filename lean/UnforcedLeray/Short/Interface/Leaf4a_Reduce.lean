import UnforcedLeray.Short.Interface.WindowSteps
import UnforcedLeray.Cons.C08PhysicalMode.Free

/-!
# Interface: step W0, the window estimate from the source form

Task `Interface:I16`. `WindowReduction` (`Short/Interface/WindowSteps.lean`) says that the
source-form window estimate `SourceWindowRegularity` (`f` a `𝒴₂` field) gives the free-form
window estimate `FreeWindowRegularity` (`g` a `𝒴₂` field with `IsWeakFreeSolution`).

Proof: `exists_projected_rep` (`Cons/C08PhysicalMode/Free.lean`) gives a periodic `𝒴₂`
representative `pg` of `τ ↦ 𝔓 g(τ)`. The integrability clauses of `IsSourceFreeSolution` for
`pg` come from those of `IsWeakFreeSolution` and `integrable_pairTerm_of_isY2`; its identity
follows from `integral_pairTerm_projected` and the identity of `IsWeakFreeSolution`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic

/-- Step W0: `WindowReduction` (the source-form window estimate gives the free-form one). -/
theorem windowReduction : WindowReduction := by
  intro hsrc h μ P w g hh hP hw hg hsol τ₀
  obtain ⟨pg, hpg, hpgae⟩ := exists_projected_rep hP hg
  have hfree : IsSourceFreeSolution h μ w pg := by
    unfold IsSourceFreeSolution
    refine ⟨fun ψ hψ => ⟨hsol.value_integrable ψ hψ, hsol.temporal_integrable ψ hψ,
      hsol.dilation_integrable ψ hψ, hsol.diffusion_integrable ψ hψ,
      integrable_pairTerm_of_isY2 hP hpg hψ⟩, fun ψ hψ => ?_⟩
    rw [integral_pairTerm_projected hP hpg hpgae hψ]
    exact hsol.identity ψ hψ
  exact hsrc h μ P w pg hh hP hw hpg hfree τ₀

end UnforcedLeray.Short.Interface
