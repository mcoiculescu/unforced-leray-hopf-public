import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm
import UnforcedLeray.Short.PartI.Tasks.AdjointInPowerDomains
import UnforcedLeray.Units.B0123

/-!
# `PartI:C11`: the canonical branch (assembly)

Source of record: `the November 2 reference manuscript`, lines 1076-1093.
Existence, asymptotics and uniqueness come from the backward continuation
(`canonical_backward_continuation`, C08); the graph-norm budget from `canonical_graphNorm_bounds`
(C10); the Riesz representative `qd` of `ℓ` lies in `𝒟(D) = X_{G,2}` by `seed_adjoint_mem_XGj`.
The bound on `(0,1]` combines the backward bound on `(0,b]` with continuity on `[b,1]`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem canonicalBranch_proof : CanonicalBranch := by
  intro lam q ℓ hI hq
  obtain ⟨qd, hl⟩ : ∃ qd : B0010.XG, ∀ f, ℓ f = inner ℂ qd f :=
    ⟨(InnerProductSpace.toDual ℂ B0010.XG).symm ℓ,
      fun f => (InnerProductSpace.toDual_symm_apply (x := f) (y := ℓ)).symm⟩
  have hqd2 : qd ∈ B0123.XGj 2 := by
    rw [B0123.XGj_eq_B0121]
    exact seed_adjoint_mem_XGj hI hl 2
  have hqd : qd ∈ B0094.D.domain := by
    rw [B0123.XGj_two] at hqd2
    exact hqd2
  obtain ⟨b, hb, W, hW, hA, hbound, huniq⟩ := canonical_backward_continuation hI hl hq hqd
  refine ⟨W, hW, hA, ?_, huniq, canonical_graphNorm_bounds hI hq hW hA⟩
  have hcont : ContinuousOn W (Icc b 1) :=
    hW.smooth.continuousOn.mono (fun x hx => lt_of_lt_of_le hb hx.1)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max (Real.exp (b * ‖B0012.L0‖) * ‖W b‖) C₂, fun θ hθ hθ1 => ?_⟩
  by_cases hθb : θ ≤ b
  · exact (hbound θ hθ hθb).trans (le_max_left _ _)
  · exact (hC₂ θ ⟨(not_le.mp hθb).le, hθ1⟩).trans (le_max_right _ _)

end UnforcedLeray.Short.PartI
