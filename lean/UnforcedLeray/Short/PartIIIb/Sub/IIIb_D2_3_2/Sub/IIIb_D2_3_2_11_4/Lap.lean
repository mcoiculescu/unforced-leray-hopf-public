import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Lap.Trace

/-!
# Laplacian equivariance (`PartIII-b:IIIb-D2/3/2/11/4`, source 6314-6316)

`lapEqv_proved`: `Δ F (g y) = g (Δ F y)` for a `C²` field `F` commuting with a linear isometry `g`,
from the trace invariance `trace_equiv` applied to the second derivative pairing `hessOp`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lapEqv_proved : LapEqv := by
  intro g F hF hG y
  unfold physLap
  exact trace_equiv g (fun y u v => hessOp F y u v) (fun y u v => hess_equiv g F hF hG y u v)
    (fun y => hess_add_left F y) (fun y => hess_smul_left F y)
    (fun y => hess_add_right hF y) (fun y => hess_smul_right hF y) y

end UnforcedLeray.Short.PartIIIb.Concrete
