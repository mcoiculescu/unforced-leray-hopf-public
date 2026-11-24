import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2.Contract
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2.ContCompact
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2.Global

/-!
# Convergence of spatial mollification in `L^p` on `(0,P] x B(0,R)` (unconditional)

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`).

The unconditional statement follows from the localisation lemma `spatMol_tendsto_lp_of`
applied to the global `L^p` convergence `spatMolGlobalLp_holds`, whose hypotheses are
discharged by `spatMolContract_holds` and `spatMolContCompact_holds`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

theorem spatMol_tendsto_lp (P : ℝ) [Fact (0 < P)] (R : ℝ) (p : ENNReal) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (f : ℝ × UnforcedLeray.Space → ℂ) (hf : MemLpLoc P f p) (ρ : ℕ → UnforcedLeray.Space → ℝ) (hρ : IsApproxId ρ) : Filter.Tendsto (fun n => eLpNorm (spatMol (ρ n) f - f) p ((volume.restrict (Ioc 0 P)).prod (volume.restrict (Metric.closedBall 0 R)))) Filter.atTop (nhds 0) :=
  spatMol_tendsto_lp_of (spatMolGlobalLp_holds spatMolContract_holds spatMolContCompact_holds)
    P R p hp hp' f hf ρ hρ

end UnforcedLeray.Short.PartIIIb.Concrete
