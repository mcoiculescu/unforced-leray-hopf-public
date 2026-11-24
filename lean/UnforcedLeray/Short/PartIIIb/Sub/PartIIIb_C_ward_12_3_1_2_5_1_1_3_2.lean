import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas

/-!
# `InletFnNearBound` from near-axis axial decay of the inlet jets and bounded raw derivatives

Source `the November 2 reference manuscript`
lines 2545-2551 (all-age heat expansion: arbitrary axial decay; inlet cutoff vanishes near the
axis), 2563-2569, 1206-1222, 1217-1219.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Axial decay of the jets of `E_i = realC (inlet)` on the disc `ϱ ≤ R₀` (2545-2549): spatial
derivatives of order `≤ 3` and spatial derivatives of order `≤ 1` of `∂_τ E` are bounded by
`C (1+|y₃|)^{-N}`, uniformly in `τ ∈ (0,P]`. -/
def InletENearJets : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (N : ℕ) (R0 : ℝ), 0 < R0 → ∃ C : ℝ,
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      (∀ k : ℕ, k ≤ 3 →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ))) ∧
      (∀ k : ℕ, k ≤ 1 →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
            UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ)))

/-- Product-rule step (2545-2551, 2563-2569): on `ϱ ≤ R₀` the weight `y` in `L₀` is
`≤ R₀ + |y₃|`, so axial decay of the jets of `E` (take `N` large) and bounded raw derivatives
of order `≤ 2` give `‖inletFn‖ ≤ C(1+|y₃|)^{-2}`. -/
def InletFnNearOfJets : Prop := InletENearJets → RawDerivBdd → InletFnNearBound

theorem inletFnNearBound_of (h1 : InletENearJets) (h2 : InletFnNearOfJets) (h3 : RawDerivBdd) :
    InletFnNearBound := h2 h1 h3

end UnforcedLeray.Short.PartIIIb.Concrete
