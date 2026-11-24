import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.Tail
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.TailGen

/-!
# `PartIII-b:C/rep/5/1/1/3`: the per-bin velocity bound (restated chain)

Source `the November 2 reference manuscript` 5585-5593 (single-term bound), with
the kernel bound `PerBinVelocitySeq` of `PartIII-b_C_rep_5_1_1Org.lean` (line 118).

The bound is obtained from the single-term estimate for all thin stresses `tailBinGenSeq`
through `perBinVelocitySeq_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The per-bin velocity bound (5585-5593), from the single-term bound for thin stresses. -/
theorem perBinVelocitySeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : PerBinVelocitySeq Pl σ₀ mZ dm dp :=
  perBinVelocitySeq_of Pl σ₀ mZ dm dp (tailBinGenSeq Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
