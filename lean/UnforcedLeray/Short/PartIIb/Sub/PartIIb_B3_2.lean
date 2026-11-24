import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Compose

/-!
# `PartII-b:B3/2`: the heat-remainder leaf (SP 2584-2628)

Statement of the open leaf `BallRemainderH2`, split off from `Tasks/HeatRemainderCore.lean` so that
the leaf proof (`Tasks/HeatRemainderH2.lean`) and the parent can both import it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- **Open leaf: the heat remainder `Q = U − H_a ∈ C_τ H²` at the contraction-ball states**
(SP 2584-2628: "`V − H_a ∈ C_per H^k ∩ X_p`" (`short-bg:raw-heat`, SP 2586-2603); "the field
`Q = U − H_a ∈ X_p` solves `A₀Q = −𝐏 div 𝕋`"; "Free uniqueness identifies `Q` with
`−∫₀^∞ S₀(t)𝐏 div 𝕋(τ − t) dt`" with the majorants
`‖D^jS₀(t)𝐏 div 𝕋‖₂ ≤ C t^{-1/2}‖𝕋‖_{H^j}` for `0 < t ≤ 1` and `≤ C e^{-3t/4}‖𝕋‖₂` for `t ≥ 1`;
"Thus `Q ∈ C_per H²`").  At every state `z` of the contraction ball (quantifiers of
`B3Stmt.AtBallStates`), with `U = bgField p z`, `a = p.datum (p.coord z)` and
`H_a = Blueprint.heatProfile p.ν a`, there is a continuous path `Q : ℝ → H²(ℝ³)` whose value at
every phase `τ` is `U(τ) − H_a(τ)` almost everywhere.  (Periodicity of `Q` is not asked: it
follows from that of `U` and `H_a`, see `ballHeatRemainder_Core_of`.) -/
def BallRemainderH2 : Prop :=
  B3Stmt.AtBallStates fun p z => ∃ Q : ℝ → UnforcedLeray.SobolevGraph.H2, Continuous Q ∧
    ∀ τ : ℝ, ((Q τ).value : SpatialField) =ᵐ[volume]
      bgField p z τ - UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ

end UnforcedLeray.Short.IIb
