import UnforcedLeray.Short.PartI.Sub.T02_1_4

/-!
# Part I, task `PartI:T02/1/4/4`: time smoothness of the mild path in every `H^m` (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the mild solution is smooth for positive time; here the
datum `trainDatum c` is smooth, solenoidal and lies in every `H^k`, so the solution is smooth up to
`s = 0`).

Target: `MildPathTimeSmooth` (`Short/PartI/Sub/T02_1_4.lean`): every `H^{k+3}`-valued lift `uk` of
the mild path `u` is `C^∞` on `[0,T]` as a function of time (one-sided at the end points).

Route.  The right-hand side of the equation `u' = νΔu - P₀(u·∇u)` is a *smooth map*
`R_k : H^{k+5} → H^{k+3}` (`Δ : H^{m+2} → H^m` bounded, `(v,w) ↦ (v·∇)w` bounded
`H^{k+5} × H^{k+5} → H^{k+4}` because `H^m` is an algebra for `m ≥ 2` in dimension two, `P₀`
bounded on `H^{k+4}`, `H^{k+4} ⊂ H^{k+3}`), and the mild equation says that the `H^{k+3}`-lift
`uk` is differentiable on `[0,T]` (one-sided) with derivative `R_k (uk₂(t))` where `uk₂` is the
`H^{k+5}`-lift of the same path.  This is the single open leaf `MildPathDerivRhs`; it needs the
`H^m` heat semigroup, `P₀` and the product estimate at all levels, none of which is in the library
(it has the `H³` versions only), so it is expected to need a further split (see the docstring of
the leaf).  The bootstrap `uk ∈ C^j ⇒ uk ∈ C^{j+1}` is proved here: persistence (`HkPersistence`,
`PartI:T02/1/2`) supplies the `H^{k+5}`-lift, the derivative is `R_k ∘ uk₂`, which is `C^j` by the
induction hypothesis at level `k + 2` and smoothness of `R_k`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- **The open leaf** (time derivative of the mild path in every `H^m`; HEAVY, source lines
261-288).  For `ν > 0`, `c ≥ 1` there is a family of smooth maps
`R_k : H^{k+5} → H^{k+3}` (independent of `T` and of the train) such that for every mild train `u`
on `[0,T]` and all lifts `ukA : C([0,T], H^{k+3})`, `ukB : C([0,T], H^{k+5})` of `u`, the lift
`ukA` is differentiable within `[0,T]` at every `t ∈ [0,T]` with derivative `R_k (ukB t)`.

Mathematics.  Take `R_k v = νΔv - P₀((v·∇)v)` with `Δ = ∂_q∘∂_q + ∂_η∘∂_η` built from
`Sob.W.partialDeriv` (`Lib/Sobolev/Space.lean`).  Since `restrict` is injective
(`Sob.W.value_injective`, `value_restrict` is `rfl`), `ukA t = restrict (ukB t)`, so the claim is
that the mild solution `u = e^{tνΔ}d - ∫_0^t e^{(t-r)νΔ}P₀ div(u⊗u) dr` with `d` in every `H^m`
and `u ∈ C([0,T], H^{k+5})` satisfies `u(t) = d + ∫_0^t R(u(r)) dr` in `H^{k+3}`, with `R∘u`
continuous into `H^{k+3}`; the identity `div(u⊗u) = (u·∇)u` uses `div u = 0` (`P₀`-fixed).
Expected further split: (a) `H^m` product estimate and `(v·∇)w` as a bounded bilinear map
`H^{m+1} × H^{m+1} → H^m` for `m ≥ 2` (the library has `tensorH3Bilinear` only); (b) `P₀` on
`H^m` commuting with derivatives and with the heat semigroup (the library has `P0H3CLM` only,
`Lib/TrainB/P0H3Operator.lean`); (c) strong continuity and the generator of the heat semigroup
on `H^m` (the library has the `H³` semigroup, `Lib/HeatCylinder/HeatVecH3Semigroup.lean:23`,
and age derivatives in `HeatVecAgeDerivative.lean`); (d) the integral form of the equation in
`H^{k+3}` for a mild solution, including the end point `t = 0` (the datum lies in every `H^m` and
is solenoidal; no compatibility condition on the cylinder). -/
def MildPathDerivRhs : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c),
    ∃ R : ∀ k : ℕ, Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) → Cyl.H ℝ Cyl.Vec2 c 0 (k + 3),
      (∀ k : ℕ, ContDiff ℝ ∞ (R k)) ∧
      ∀ (T : ℝ) (hT : 0 < T) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
        IsMildTrain ν c T hν hc hc1 hT u → ∀ k : ℕ,
        ∀ (ukA : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)))
          (ukB : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3))),
          (∀ t, Sob.W.restrict (Nat.le_add_left 3 k) (ukA t) = u t) →
          (∀ t, Sob.W.restrict (Nat.le_add_left 3 (k + 2)) (ukB t) = u t) →
          ∀ t ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (extendCompactPath hT.le ukA)
              (R k (extendCompactPath hT.le ukB t)) (Icc (0 : ℝ) T) t

/-- **`MildPathTimeSmooth` from persistence and the derivative leaf.**  Induction on the order of
smoothness: `uk ∈ C^j` for every level `k` and every lift gives `uk ∈ C^{j+1}`, since
`derivWithin uk = R_k ∘ uk₂` on `[0,T]` with `uk₂` the `H^{k+5}`-lift supplied by `HkPersistence`. -/
theorem mildPathTimeSmooth_of (hP : HkPersistence) (hR : MildPathDerivRhs) :
    MildPathTimeSmooth := by
  intro ν c T hν hc hc1 hT u hu k uk huk
  have hper := hP ν c T hν hc hc1 hT u hu
  obtain ⟨R, hRsm, hRder⟩ := hR ν c hν hc hc1
  have key : ∀ j : ℕ, ∀ (k : ℕ)
      (uk : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (k + 3))),
      (∀ t, Sob.W.restrict (Nat.le_add_left 3 k) (uk t) = u t) →
      ContDiffOn ℝ (j : WithTop ℕ∞) (extendCompactPath hT.le uk) (Icc (0 : ℝ) T) := by
    intro j
    induction j with
    | zero =>
      intro k uk _
      rw [Nat.cast_zero, contDiffOn_zero]
      exact (extendCompactPath hT.le uk).continuous.continuousOn
    | succ j ih =>
      intro k uk huk
      obtain ⟨ukB, hukB⟩ := hper (k + 2)
      have hder := hRder T hT u hu k uk ukB huk hukB
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
      refine ⟨fun t ht => (hder t ht).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
      have hcongr : EqOn (derivWithin (extendCompactPath hT.le uk) (Icc (0 : ℝ) T))
          (fun t => R k (extendCompactPath hT.le ukB t)) (Icc (0 : ℝ) T) := by
        intro t ht
        exact (hder t ht).derivWithin ((uniqueDiffOn_Icc hT) t ht)
      have hsm : ContDiff ℝ (j : WithTop ℕ∞) (R k) := (hRsm k).of_le (mod_cast le_top)
      exact (hsm.comp_contDiffOn (ih (k + 2) ukB hukB)).congr hcongr
  exact contDiffOn_infty.2 fun j => key j k uk huk

end UnforcedLeray.Short.PartI
