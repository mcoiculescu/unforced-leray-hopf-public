import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIa.StatementsRing

/-!
# `RingLiftBdd` from Part II-a `RingBoundedDerivs` (task `PartIII-b:C/ward/12/3/1/2/6/1/3/1`)

Source `the November 2 reference manuscript`
lines 1217-1219 ("globally bounded fixed spatial derivatives" of `U_R`) and 1322-1325
("`‖U_R‖_{W^{k,∞}} ≤ P_k`, uniformly for `R ≥ 2`").

`RingLiftBdd` asks only for the orders `k = 0, 1, 2`, which `Short.PartIIa.RingBoundedDerivs`
(task `PartII-a:R07`) gives at the single order `2` (it bounds every `j ≤ k` below one threshold),
taken at `ρ = 2` (`c = ν⁻²`, the train of `Params`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set
open scoped ContDiff
open UnforcedLeray

/-- **`RingLiftBdd` from `RingBoundedDerivs`** (source 1217-1219, 1322-1325): apply
`RingBoundedDerivs` at `ρ = 2` and order `2`; its smooth extension `U τ` is the lift, and its bound
`polyConst C d ν (ν^{-2})` serves the orders `0, 1, 2`. -/
theorem ringLiftBdd_of_ringBoundedDerivs (h : Short.PartIIa.RingBoundedDerivs) : RingLiftBdd := by
  obtain ⟨ν₀, hν₀, C, d, H⟩ := h 2 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν hν ψ pr hpr R hR => ?_⟩
  obtain ⟨U, hU, hoff, hB⟩ := H ν hν ψ pr hpr R hR
  exact ⟨fun x => U x.1 x.2, fun τ => hU τ, fun x hx => hoff x.1 x.2 hx,
    fun k => ⟨_, fun τ y => hB k (Nat.le_of_lt_succ k.isLt) τ y⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.ringLiftBdd_of_ringBoundedDerivs
