import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Units.B0063

/-!
# Part I, task `PartI:S13a/6`: the converse generator inclusion

Source of record: `the November 2 reference manuscript`, lines 841-852 ("the
converse inclusion follows from `T(t)f - f = -∫₀ᵗ T(s) Ω∂_ϑ f ds`"). Target:
`freeFlowGeneratorConverse j : FreeFlowGeneratorConverse j` (`Short/PartI/Sub/S13a.lean`).

Proof route. Any family `T` representing the free flow equals the library group
`UnforcedLeray.B0062.transport j M` (as in the sibling `GeneratorForward.lean`). If the difference
quotients `t⁻¹ • (T t F - F)` converge to `G` along `𝓝[≠] 0`, they converge along `𝓝[>] 0`, so
`t ↦ T(t)F` has right derivative `G` at `0`. The library unit B0063 gives
`hasWeakTransport_of_hasDerivWithinAt`: a right derivative `-G'` at `0` yields
`HasWeakTransport F.value G'.value`. Taking `G' = -G` gives `F ∈ transportDomain` and
`transport ⟨F, hF⟩ = -G` (`B0009.transport_eq`), i.e. `-(transport ⟨F, hF⟩) = G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The Cartesian free flow is the library flow `B0062.flow`. -/
theorem fcv_freeFlow_eq_flow (t : ℝ) (f : ℂ → ℂ) (y : ℂ) :
    freeFlow t f y = f (UnforcedLeray.B0062.flow t y) := by
  have hΩ : B0009.Omega y = UnforcedLeray.B0062.Omega ‖y‖ := rfl
  have h : (-(t * B0009.Omega y) : ℝ) = -(UnforcedLeray.B0062.Omega ‖y‖ * t) := by
    rw [hΩ, mul_comm]
  unfold freeFlow
  rw [UnforcedLeray.B0062.flow, UnforcedLeray.B0062.phase, UnforcedLeray.B0062.gexp, h]

/-- Any family representing the free flow equals the library transport group `B0062.transport`. -/
theorem fcv_transport_eq_of_rep {j : ℕ} {M : ℝ}
    (T : ℝ → (UnforcedLeray.B0008.HjM j M →L[ℂ] UnforcedLeray.B0008.HjM j M))
    (hrep : ∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ))
    (t : ℝ) (F : UnforcedLeray.B0008.HjM j M) :
    T t F = UnforcedLeray.B0062.transport j M t F := by
  apply UnforcedLeray.B0008.HjM.ext
  apply UnforcedLeray.B0062.L2w_eq_of_ae
  filter_upwards [hrep t F, UnforcedLeray.B0062.transport_value t F] with y e1 e2
  rw [e1, e2, fcv_freeFlow_eq_flow]

/-- **Generator, converse inclusion** (`FreeFlowGeneratorConverse j`, source lines 841-852). -/
theorem freeFlowGeneratorConverse (j : ℕ) : FreeFlowGeneratorConverse j := by
  unfold FreeFlowGeneratorConverse
  intro M _hM T hrep F G hlim
  have hT : ∀ t, T t F = UnforcedLeray.B0062.transport j M t F :=
    fun t => fcv_transport_eq_of_rep T hrep t F
  have hlim' : Tendsto (fun t : ℝ => t⁻¹ • (UnforcedLeray.B0062.transport j M t F - F))
      (𝓝[≠] 0) (𝓝 G) :=
    Tendsto.congr (fun t => congrArg (fun x => t⁻¹ • (x - F)) (hT t)) hlim
  have hright : Tendsto (fun t : ℝ => t⁻¹ • (UnforcedLeray.B0062.transport j M t F - F))
      (𝓝[>] 0) (𝓝 G) :=
    hlim'.mono_left (nhdsWithin_mono _ fun t ht => (Set.mem_Ioi.1 ht).ne')
  have hder : HasDerivWithinAt (fun t => UnforcedLeray.B0062.transport j M t F) G (Ici 0) 0 :=
    (UnforcedLeray.B0063.hasDerivWithinAt_iff_tendsto_quotient F G).2 hright
  have hder' : HasDerivWithinAt (fun t => UnforcedLeray.B0062.transport j M t F)
      (-(-G)) (Ici 0) 0 := by
    rw [neg_neg]
    exact hder
  have hw : B0009.HasWeakTransport F.value (-G).value :=
    UnforcedLeray.B0063.hasWeakTransport_of_hasDerivWithinAt hder'
  have hF : F ∈ B0009.transportDomain j M := ⟨-G, hw⟩
  refine ⟨hF, ?_⟩
  have htr : B0009.transport (⟨F, hF⟩ : B0009.transportDomain j M) = -G :=
    B0009.transport_eq hw
  rw [htr, neg_neg]

end UnforcedLeray.Short.PartI
