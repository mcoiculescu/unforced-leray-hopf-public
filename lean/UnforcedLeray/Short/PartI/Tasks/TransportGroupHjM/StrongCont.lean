import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Units.B0063.Strong

/-!
# Part I, task `PartI:TransportGroupHjM`: strong continuity of the free flow on `H^j_M`

Source of record: `the November 2 reference manuscript`, lines 841-852 ("density").
Target: `FreeFlowStrongCont j` (`Short/PartI/Sub/S13a.lean`): every family `T(t)` of bounded
operators on `H^j_M` (`M > 1`) that represents the free flow almost everywhere, with the polynomial
bound `‖T(t)‖ ≤ C (1+|t|)^j`, is strongly continuous.

**Proof used here.** The library already proves strong continuity of the transport group
`B0062.transport j M` on `H^j_M` (`B0063.continuous_transport_apply`, via the iterated chain rule
of B0062 and continuity of `g ↦ g ∘ Φ_t` on `L²(⟨y⟩^{2M})`; no density theorem is needed). Any
`T` as in the hypothesis agrees with `B0062.transport j M` on every `F`: both have function
`F ∘ Φ_t` almost everywhere, and `HjM.value_injective` identifies elements of `H^j_M` by their
function. So `t ↦ T(t)F` is the continuous curve `t ↦ B0062.transport j M t F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- `freeFlow t f = f ∘ B0062.flow t` as functions on the plane (source lines 841-852). The
Omega-conventions agree: `B0009.Omega y = B0062.Omega ‖y‖ = Real.exp (-(‖y‖ ^ 2 / 4))`. -/
theorem freeFlow_eq_comp_B0062flow (t : ℝ) (f : ℂ → ℂ) (y : ℂ) :
    freeFlow t f y = f (UnforcedLeray.B0062.flow t y) := by
  have hO : B0009.Omega y = UnforcedLeray.B0062.Omega ‖y‖ := rfl
  have hm : -(t * B0009.Omega y) = -(UnforcedLeray.B0062.Omega ‖y‖ * t) := by
    rw [hO]
    ring
  simp only [freeFlow, UnforcedLeray.B0062.flow, UnforcedLeray.B0062.phase,
    UnforcedLeray.B0062.gexp, hm]

/-- **Strong continuity of the free flow on `H^j_M`** (source lines 841-852, "density"): any
family `T` representing the free flow a.e. with the polynomial bound is strongly continuous.
Proof: `T t F` and `B0062.transport j M t F` have a.e. equal functions (both `F ∘ Φ_t`), hence
are equal in `H^j_M` (`HjM.value_injective`, `Lp.ext`, `wMeasure_ac`); so the curve
`t ↦ T t F` is the continuous curve `B0063.continuous_transport_apply`. -/
theorem freeFlowStrongCont (j : ℕ) : FreeFlowStrongCont j := by
  unfold FreeFlowStrongCont
  intro M _hM T hrep _hbd F
  have key : ∀ t : ℝ, T t F = UnforcedLeray.B0062.transport j M t F := by
    intro t
    have hae : ((T t F).value : ℂ → ℂ) =ᵐ[volume]
        ((UnforcedLeray.B0062.transport j M t F).value : ℂ → ℂ) := by
      filter_upwards [hrep t F, UnforcedLeray.B0062.transport_value t F] with y h1 h2
      rw [h1, h2, freeFlow_eq_comp_B0062flow]
    exact UnforcedLeray.B0008.HjM.value_injective
      (Lp.ext ((UnforcedLeray.B0008.wMeasure_ac M).ae_le hae))
  have hfun : (fun t : ℝ => T t F) = fun t => UnforcedLeray.B0062.transport j M t F :=
    funext key
  rw [hfun]
  exact UnforcedLeray.B0063.continuous_transport_apply F

end UnforcedLeray.Short.PartI
