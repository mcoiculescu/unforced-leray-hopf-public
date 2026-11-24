import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Zero
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Succ
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Group
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.StrongCont
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.GeneratorForward
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.GeneratorConverse

/-!
# Part I, task `PartI:S13a` (unconditional): the free transport group on `H^j_M`

Source of record: `the November 2 reference manuscript`, lines 841-852.

The free transport `T(t)f(r, ϑ) = f(r, ϑ - Ω(r)t)` is a strongly continuous group on `H^j_M`
(`M > 1`) with polynomial norm bound `‖T(t)‖ ≤ C_j (1+|t|)^j`. Its generator has domain
`B0009.transportDomain j M` and acts there as `-Ω∂_ϑ = -B0009.transport`. The sign is minus:
`T(t)f(r, ϑ) = f(r, ϑ - Ω t)` has generator `-Ω ∂_ϑ`.

Proof. The existence of the representing family is proved for every `j` by induction, with
`freeFlowExists_zero` as base and `freeFlowExists_succ` as step. The remaining five properties
come from the lemma files `Tasks/TransportGroupHjM/*.lean` through the conditional theorem
`transport_group_HjM_of` in `Sub/S13a.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The free-flow representation exists for every order `j`, by induction on `j`. -/
theorem freeFlowExists_all : ∀ j : ℕ, FreeFlowExists j
  | 0 => freeFlowExists_zero
  | j + 1 => freeFlowExists_succ j (freeFlowExists_all j)

/-- **The free transport group on `H^j_M`** (source lines 841-852): `T(t)f(r, ϑ) = f(r, ϑ - Ω(r)t)`
is a strongly continuous group on `H^j_M` (`M > 1`) with `‖T(t)‖ ≤ C_j (1+|t|)^j`, its generator
has domain `B0009.transportDomain j M` (`F` is in the domain iff the difference quotients
converge in `H^j_M`) and acts there as `-Ω∂_ϑ = -B0009.transport`. -/
theorem transport_group_HjM (j : ℕ) {M : ℝ} (hM : 1 < M) :
    ∃ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
      (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) ∧
      (∀ s t, T (s + t) = T s * T t) ∧ T 0 = 1 ∧
      (∀ F, Continuous fun t => T t F) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C * (1 + |t|) ^ j) ∧
      (∀ F : B0008.HjM j M, F ∈ B0009.transportDomain j M ↔
        ∃ G : B0008.HjM j M,
          Tendsto (fun t : ℝ => t⁻¹ • (T t F - F)) (𝓝[≠] 0) (𝓝 G)) ∧
      (∀ (F : B0008.HjM j M) (hF : F ∈ B0009.transportDomain j M),
        Tendsto (fun t : ℝ => t⁻¹ • (T t F - F)) (𝓝[≠] 0)
          (𝓝 (-(B0009.transport (⟨F, hF⟩ : B0009.transportDomain j M))))) := by
  exact transport_group_HjM_of (freeFlowExists_all j) (freeFlowGroup j) (freeFlowStrongCont j)
    (freeFlowGeneratorForward j) (freeFlowGeneratorConverse j) hM

end UnforcedLeray.Short.PartI
