import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core

/-!
# Source fact behind `RingLiftDerivBddOfSmooth`: the off-axis `W^{k,∞}` bound

Source `the November 2 reference manuscript`
lines 1305-1325.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

/-- **Off-axis derivative bound for the similarity lift** (source lines 1305-1325: term-by-term
heat expansion of `r a_{2j} ∂_η^{2j} G`, remainder `O(r^{2N+4-a})`, Gaussian-flat fluctuations,
finite expansion order `N_k`, DSS periodicity `2c/R`; "the same argument ... proves
`‖U_R‖_{W^{k,∞}} ≤ P_k`"): below one threshold `ν₀` (independent of `k`), for the `ρ = 2` exact
train and `R ≥ 2`, every Cartesian derivative of order `k` of the lift `y ↦ U_R(τ, y)`, taken at
points off the axis, is bounded uniformly in `τ` and `y`. -/
def RingLiftOffAxisDerivBdd : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : B0184.ProfilePoint → ℝ,
    Short.PartIIa.IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R → ∀ k : ℕ,
      ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), Axi.ϱ y ≠ 0 →
        ‖iteratedFDeriv ℝ k (B0190.simProfile 1 (B0185.liftVelocity R ψ) τ) y‖ ≤ C

end UnforcedLeray.Short.PartIIIb.Concrete
