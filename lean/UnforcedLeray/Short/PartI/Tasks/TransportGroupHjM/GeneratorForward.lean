import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Units.B0063

/-!
# Part I, task `PartI:TransportGroupHjM`: the forward generator inclusion

Source of record: `the November 2 reference manuscript`, lines 841-852 ("density and
differentiation of the flow give the generator domain"). Target: `FreeFlowGeneratorForward j`
(`Short/PartI/Sub/S13a.lean`).

Proof route. Any family `T` representing the free flow agrees with the library transport group
`UnforcedLeray.B0062.transport j M` (unit B0062): both have values almost everywhere equal to
`F ∘ Φ_t`, so they are equal in `H^j_M`. The library unit B0063 proves
`hasDerivAt_transport_of_hasWeakTransport`: if `D_E F = G` weakly then `t ↦ T(t)F` has derivative
`-G` at `0`. The difference quotient limit is then the derivative at `0` (slope form).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The Cartesian free flow is the library flow `B0062.flow`. -/
theorem gfw_freeFlow_eq_flow (t : ℝ) (f : ℂ → ℂ) (y : ℂ) :
    freeFlow t f y = f (UnforcedLeray.B0062.flow t y) := by
  have hΩ : B0009.Omega y = UnforcedLeray.B0062.Omega ‖y‖ := rfl
  have h : (-(t * B0009.Omega y) : ℝ) = -(UnforcedLeray.B0062.Omega ‖y‖ * t) := by
    rw [hΩ, mul_comm]
  unfold freeFlow
  rw [UnforcedLeray.B0062.flow, UnforcedLeray.B0062.phase, UnforcedLeray.B0062.gexp, h]

/-- Any family representing the free flow equals the library transport group `B0062.transport`. -/
theorem gfw_transport_eq_of_rep {j : ℕ} {M : ℝ}
    (T : ℝ → (UnforcedLeray.B0008.HjM j M →L[ℂ] UnforcedLeray.B0008.HjM j M))
    (hrep : ∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ))
    (t : ℝ) (F : UnforcedLeray.B0008.HjM j M) :
    T t F = UnforcedLeray.B0062.transport j M t F := by
  apply UnforcedLeray.B0008.HjM.ext
  apply UnforcedLeray.B0062.L2w_eq_of_ae
  filter_upwards [hrep t F, UnforcedLeray.B0062.transport_value t F] with y e1 e2
  rw [e1, e2, gfw_freeFlow_eq_flow]

/-- **Generator, forward inclusion** (`FreeFlowGeneratorForward j`, source lines 841-852). -/
theorem freeFlowGeneratorForward (j : ℕ) : FreeFlowGeneratorForward j := by
  unfold FreeFlowGeneratorForward
  intro M _hM T hrep _hbd _hcont F hF
  have hd := UnforcedLeray.B0063.hasDerivAt_transport_of_hasWeakTransport
    (F := F) (G := B0009.transport (⟨F, hF⟩ : B0009.transportDomain j M))
    (B0009.hasWeakTransport_transport (⟨F, hF⟩ : B0009.transportDomain j M))
  have hF0 : UnforcedLeray.B0062.transport j M 0 F = F := by
    simp [UnforcedLeray.B0062.transport_zero]
  have key := hd.tendsto_slope_zero
  refine Tendsto.congr (fun t => ?_) key
  show t⁻¹ • (UnforcedLeray.B0062.transport j M (0 + t) F - UnforcedLeray.B0062.transport j M 0 F) =
    t⁻¹ • (T t F - F)
  rw [zero_add, hF0, gfw_transport_eq_of_rep T hrep t F]

end UnforcedLeray.Short.PartI
