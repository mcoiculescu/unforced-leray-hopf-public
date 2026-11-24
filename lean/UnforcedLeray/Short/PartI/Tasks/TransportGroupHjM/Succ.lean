import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Units.B0062

/-!
# Part I, task `PartI:TransportGroupHjM`, succ step: `FreeFlowExists j → FreeFlowExists (j + 1)`

Source of record: `the November 2 reference manuscript`, lines 841-852
("the chain rule gives `‖T(t)‖ ≤ C_j (1+|t|)^j`").


`UnforcedLeray.B0062`: `B0062.transport j M t` is a bounded operator on `H^j_M`, its function is
`f ∘ B0062.flow t` almost everywhere (`B0062.transport_value`), and
`‖T(t)‖ ≤ C_j (1+|t|)^j` (`B0062.norm_transport_le`). Hence the conclusion holds with the
operators `B0062.transport (j + 1) M`, and the hypothesis `FreeFlowExists j` is not used.

The two phase conventions agree: `B0009.Omega y = GaussianVortex.radialOmega ‖y‖` and
`B0062.Omega ‖y‖` are both `Real.exp (-(‖y‖ ^ 2 / 4))`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- `freeFlow t f = f ∘ B0062.flow t` as functions on the plane. -/
theorem freeFlow_eq_flow_comp_succ (t : ℝ) (f : ℂ → ℂ) :
    freeFlow t f = fun y => f (UnforcedLeray.B0062.flow t y) := by
  funext y
  have hO : B0009.Omega y = UnforcedLeray.B0062.Omega ‖y‖ := rfl
  have hm : -(t * B0009.Omega y) = -(UnforcedLeray.B0062.Omega ‖y‖ * t) := by
    rw [hO]
    ring
  simp only [freeFlow, UnforcedLeray.B0062.flow, UnforcedLeray.B0062.phase,
    UnforcedLeray.B0062.gexp, hm]

/-- **Succ step of the free flow** (source lines 841-852): if `FreeFlowExists j` holds, then so
does `FreeFlowExists (j + 1)`. The witnesses are `B0062.transport (j + 1) M`, with the a.e.
representation `f ∘ Φ_t` and the bound `C (1+|t|)^(j+1)` from `B0062.norm_transport_le`. -/
theorem freeFlowExists_succ (j : ℕ) : FreeFlowExists j → FreeFlowExists (j + 1) := by
  intro _
  unfold FreeFlowExists
  intro M _hM
  obtain ⟨C, hC0, hC⟩ := UnforcedLeray.B0062.norm_transport_le (j + 1) M
  refine ⟨fun t => UnforcedLeray.B0062.transport (j + 1) M t, fun t F => ?_, C, hC0, hC⟩
  rw [freeFlow_eq_flow_comp_succ]
  exact UnforcedLeray.B0062.transport_value t F

end UnforcedLeray.Short.PartI
