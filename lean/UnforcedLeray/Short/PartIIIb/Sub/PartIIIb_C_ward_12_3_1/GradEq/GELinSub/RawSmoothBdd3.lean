import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIa.StatementsRing

/-!
# `U_raw ∈ W^{3,∞}`: the order-3 versions of `RingLiftBdd`, `RawDerivBdd`, `RawSmoothBdd`

Organizer item `ORG:ward/bg-bootstrap` (input of the linear leaf `GELin2`, task

the November 2 reference manuscript` lines 1217-1219 ("globally bounded fixed spatial derivatives" of
`U_R`), 1322-1325 ("`‖U_R‖_{W^{k,∞}} ≤ P_k`, uniformly for `R ≥ 2`"), 2552-2559 (the second
differentiated equation contains `w·∇∂²V`, so `V ∈ W^{3,∞}` is used).

The first-order versions (`RingLiftBdd`, `RawDerivBdd`, `RawSmoothBdd`) bound the orders
`k = 0, 1, 2`; here `k : Fin 4` bounds the orders `0, …, 3`, from `RingBoundedDerivs` (task
`PartII-a:R07`) at the single order `3`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set
open scoped ContDiff
open UnforcedLeray
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **`U_R ∈ W^{3,∞}`** (source 1217-1219, 1322-1325): as `RingLiftBdd`, with the spatial
derivatives of orders `k = 0, 1, 2, 3` (`k : Fin 4`) of the smooth extension bounded uniformly in
`(τ, y)` (`ρ = 2`, i.e. `c = ν⁻²`, `R ≥ 2`). -/
def RingLiftBdd3 : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : B0184.ProfilePoint → ℝ,
    Short.PartIIa.IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R →
      ∃ U : ℝ × Space → Space, (∀ τ, ContDiff ℝ ∞ (fun y => U (τ, y))) ∧
        (∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
          U x = B0190.simProfile 1 (B0185.liftVelocity R ψ) x.1 x.2) ∧
        ∀ k : Fin 4, ∃ C : ℝ, ∀ (τ : ℝ) (y : Space),
          ‖iteratedFDeriv ℝ (k : ℕ) (fun y => U (τ, y)) y‖ ≤ C

/-- **`RingLiftBdd3` from `RingBoundedDerivs`** (source 1217-1219, 1322-1325): apply
`RingBoundedDerivs` at `ρ = 2` and order `3`; its bound `polyConst C d ν (ν^{-2})` serves the
orders `0, …, 3`. -/
theorem ringLiftBdd3_of_ringBoundedDerivs (h : Short.PartIIa.RingBoundedDerivs) :
    RingLiftBdd3 := by
  obtain ⟨ν₀, hν₀, C, d, H⟩ := h 2 3 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν hν ψ pr hpr R hR => ?_⟩
  obtain ⟨U, hU, hoff, hB⟩ := H ν hν ψ pr hpr R hR
  exact ⟨fun x => U x.1 x.2, fun τ => hU τ, fun x hx => hoff x.1 x.2 hx,
    fun k => ⟨_, fun τ y => hB k (Nat.le_of_lt_succ k.isLt) τ y⟩⟩

/-- Globally bounded spatial derivatives of `raw τ` of orders `k = 0, …, 3` (`k : Fin 4`), below
one threshold `ν₀`, in the background regime (source 1217-1219, 1322-1325). -/
def RawDerivBdd3 : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ k : Fin 4, ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space),
        ‖iteratedFDeriv ℝ (k : ℕ) (p.raw τ) y‖ ≤ C

/-- `RawDerivBdd3` from `RingLiftBdd3` (the argument of `rawDerivBdd_of`). -/
theorem rawDerivBdd3_of (h : RingLiftBdd3) : RawDerivBdd3 := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨min (ν₀ / 2) dm, lt_min (by linarith) hdm, fun p d hreg hν k => ?_⟩
  have hb := hreg.train_buc
  have hν1 : p.ν ≤ ν₀ / 2 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ dm := hν.trans (min_le_right _ _)
  obtain ⟨U, hU, hoff, hB⟩ := H p.ν ⟨p.ν_pos, by linarith⟩ _ _
    (UnforcedLeray.Short.IIb.isExactPlanarTrain_params_rpow p hb hreg.c_eq) p.R
    (R_ge_two hreg hν2)
  have hcont : ∀ τ, Continuous (fun y => U (τ, y)) := fun τ => (hU τ).continuous
  obtain ⟨C, hC⟩ := hB k
  refine ⟨C, fun τ y => ?_⟩
  rw [raw_eq_of hb U hcont hoff τ]
  exact hC τ y

/-- **`U_raw` smooth, periodic and in `W^{3,∞}`** (source 1214-1219, 1305-1325): as
`RawSmoothBdd`, with the spatial derivatives of orders `k = 0, …, 3` bounded. -/
def RawSmoothBdd3 : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) ∧
      (∀ τ y, p.raw (τ + p.period) y = p.raw τ y) ∧
      ∀ k : Fin 4, ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space),
        ‖iteratedFDeriv ℝ (k : ℕ) (p.raw τ) y‖ ≤ C

/-- `RawSmoothBdd3` from joint smoothness, periodicity and the order-3 bounds. -/
theorem rawSmoothBdd3_of (h1 : RawJointSmooth) (h2 : RawPeriodicAll) (h3 : RawDerivBdd3) :
    RawSmoothBdd3 := by
  intro dm dp hdm
  obtain ⟨a, ha, H1⟩ := h1 dm dp hdm
  obtain ⟨b, hb, H2⟩ := h2 dm dp hdm
  obtain ⟨c, hc, H3⟩ := h3 dm dp hdm
  refine ⟨min a (min b c), lt_min ha (lt_min hb hc), fun p d hreg hν => ?_⟩
  exact ⟨H1 p d hreg (hν.trans (min_le_left _ _)),
    H2 p d hreg (hν.trans ((min_le_right _ _).trans (min_le_left _ _))),
    H3 p d hreg (hν.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩

end UnforcedLeray.Short.PartIIIb.Concrete
