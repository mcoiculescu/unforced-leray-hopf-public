import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.Leaves
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.IntLimit
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.RankLimit

/-!
# Leaf B4 (`PartIII-a:T21/c3/2/1/1/org/3/b/4`): norm convergence of the damped interaction

Source: `the November 2 reference manuscript` (SP) 2898-2925, 2974-2978.

In the successive limit, uniformly in the train, the entrance time and `τ ∈ [0, B]`, the damped
complement interaction `A_rel(τ)` (cell zero extension of `movLInt + movFrameRankPert`,
`eq:short-causal-damped-complement`) converges in operator norm on `L²_m` to the planar damped
interaction `A0 = couplingW + Σ_i (γ - 1 - λ_i) ℓ_i(·) e_i`.

Helpers (folder `PartIII-a_T21_c3_2_1_1_org3_b_L4/`):
* `Leaves`: the interaction and finite-rank leaves and the assembly `planarDampedIntLimit_of`
  (bounds on the dense smooth class give the operator-norm bound);
* `IntPlanar`, `IntLimit`: `movLInt → couplingW` (image estimates: `couplingW = -(K W)·∇E₀`, the
  cylinder-to-plane kernel bound of Part II-b, the rescaled train comparison);
* `RankAux`, `RankAux2`, `RankInst`, `RankLimit`: `E → e`, `Λ → ℓ`, `H₀ → λΛ`, `K₀ → λE`,
  `M₀ → diag λ`, `β₀ → γ` (dual estimates, Gram inverse, lattice tails).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit

namespace OrgSplit3

namespace PlanarB

/-- **Leaf B4 (SP 2898-2925, 2974-2978)**: `PlanarDampedIntLimit` holds. -/
theorem planarDampedIntLimit_proof (κ : PlanarFrameKernels) : PlanarDampedIntLimit κ :=
  L4.planarDampedIntLimit_of κ L4.intLimitLeaf (L4.rankLimitLeaf κ)

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
