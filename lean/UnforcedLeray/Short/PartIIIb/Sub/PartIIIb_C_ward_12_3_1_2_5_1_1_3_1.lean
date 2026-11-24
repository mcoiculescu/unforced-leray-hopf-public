import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas

/-!
# `InletFnFarDecay` from far-field jets of the inlet and bounded raw derivatives

Source `the November 2 reference manuscript`
lines 2542-2548 (unprojected derivatives of the inlet bounded by `C_{k,N} ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`),
2563-2569, 1206-1222, 1217-1219 (raw derivatives bounded).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Far-field Cartesian jets of `E_i = realC (inlet)` (2542-2548): spatial derivatives of order
`k ≤ 3` bounded by `ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`, and `∂_τ E` (one `ϱ` weaker, as `∂_τ` acts like
`y·∇`) with spatial derivatives of order `k ≤ 1` bounded by `ϱ^{-2-k}(1+|y₃|/ϱ)^{-N}`;
uniform in `τ ∈ (0,P]`, for `ϱ > R₀`. -/
def InletEFarJets : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (N : ℕ), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
      (∀ k : ℕ, k ≤ 3 →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤
          C * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-(3 + (k : ℝ))) *
            (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-(N : ℝ)))) ∧
      (∀ k : ℕ, k ≤ 1 →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
            UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤
          C * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-(2 + (k : ℝ))) *
            (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-(N : ℝ))))

/-- Product-rule step (2542-2548, 2563-2569): `inletFn = -∂_j(L₀E + (raw·∇)E + (E·∇)raw)`
involves `E` up to order 3 (weight `y` of `y·∇` in `L₀`, absorbed by `ϱ(1+|y₃|/ϱ)`), `∂_τE`
to order 1, and `raw` to order 2 (`raw` jointly smooth in `(τ,y)`, `RawJointSmooth`, 2563-2569, so that
the derivatives are genuine); so far-field jets of `E` and bounded raw derivatives give the
far envelope (take `N` large). -/
def InletFnFarOfJets : Prop := InletEFarJets → RawJointSmooth → RawDerivBdd → InletFnFarDecay

theorem inletFnFarDecay_of (h1 : InletEFarJets) (h2 : InletFnFarOfJets) (h3 : RawDerivBdd)
    (h4 : RawJointSmooth) : InletFnFarDecay := h2 h1 h4 h3

end UnforcedLeray.Short.PartIIIb.Concrete
