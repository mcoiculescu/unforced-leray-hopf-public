import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1

/-!
# `RingChartRawVal`: decomposition (`PartIII-b:C/rep/8/2/1/1`)

Source `the November 2 reference manuscript`
lines 2073-2077 (`U_raw = √s[v₁e_r + (v₂ + εH)e_z]`, `H = (1-K_age)ψ`), 5460-5461, 5464-5465.

Three pieces:
* `RingChartBridge`: at the chart point `p = (s,(q,η))` the point `y = (R/√s,0,η/√s)` is off the
  axis, `chart R τ y = p`, `e_r = e₁`, `e_z = e₃` at azimuth `0`, hence
  `U_raw(τ,y) = √s · (b₀, 0, b₁)` with `b = rawProfile ε v ψ p`.
* `TrainStreamSmooth`: the decaying stream is `C^∞` jointly in `(σ,q,η)`, `σ = log s` (source
  2040-2056: the train is smooth and `ψ` is its decaying stream; the structure `IsTrain` records
  only differentiability of `ψ(s,·)` for each `s`).
* `RaisedStreamBound`: `|ψ - η∂_ηψ - 2s∂_sψ| ≤ 3𝔴₃` from the order-`≤1` jets of `ψ` in
  `(σ,q,η)` (`s∂_s = ∂_σ`, `(1+|η|)³ ≥ 1+|η|`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The ring-chart bridge at azimuth `0` (2073-2077, 5460-5461). -/
def RingChartBridge : Prop :=
  ∀ (Pl : PlanarData) (L : ReturnLevel) (p : Chart), 0 < p.1 →
    rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) =
      Real.sqrt p.1 • vecSp
        ![(UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ p) 0, 0,
          (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ p) 1]

/-- The decaying stream of the actual train is jointly `C^∞` in `(σ, q, η)`, `σ = log s`
(source 2040-2056). -/
def TrainStreamSmooth : Prop :=
  ∀ L : ReturnLevel, ContDiff ℝ (⊤ : ℕ∞) (trainFpsi L)

/-- `|H| ≤ 3𝔴₃`, `H = ψ - η∂_ηψ - 2s∂_sψ`, given joint smoothness of the stream in
`(σ,q,η)` (source 5464-5465). -/
def RaisedStreamBound : Prop :=
  ∀ L : ReturnLevel, ContDiff ℝ (⊤ : ℕ∞) (trainFpsi L) → ∀ p : Chart, 0 < p.1 →
    |UnforcedLeray.Cons.C03.raisedStream L.train.ψ p.1 p.2.1 p.2.2| ≤ 3 * trainWeight 3 L p

theorem ringChartRawVal_of (h1 : RingChartBridge) (h2 : RaisedStreamBound)
    (h3 : TrainStreamSmooth) : RingChartRawVal := by
  refine ⟨3, fun Pl L hε p hp hp1 => ?_⟩
  have hb := h1 Pl L p hp
  have hH := h2 L (h3 L) p hp
  have hε0 := L.ε_pos
  have hw := trainWeight_nonneg 3 L p
  rw [hb, ← smul_sub]
  have hv : vecSp ![(UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ p) 0, 0,
          (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ p) 1] -
        vecSp (emb (trainV L p.1 p.2)) =
      vecSp ![0, 0, L.ε * UnforcedLeray.Cons.C03.raisedStream L.train.ψ p.1 p.2.1 p.2.2] := by
    ext i
    fin_cases i <;>
      simp [vecSp, emb, trainV, UnforcedLeray.Cons.C03.rawProfile_zero,
        UnforcedLeray.Cons.C03.rawProfile_one]
  rw [hv, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hn : ‖vecSp ![0, 0, L.ε * UnforcedLeray.Cons.C03.raisedStream L.train.ψ p.1 p.2.1 p.2.2]‖ =
      L.ε * |UnforcedLeray.Cons.C03.raisedStream L.train.ψ p.1 p.2.1 p.2.2| := by
    rw [vecSp, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hε0]
  rw [hn]
  have hs := Real.sqrt_nonneg p.1
  simp only [pow_zero, mul_one]
  calc Real.sqrt p.1 * (L.ε * |UnforcedLeray.Cons.C03.raisedStream L.train.ψ p.1 p.2.1 p.2.2|)
      ≤ Real.sqrt p.1 * (L.ε * (3 * trainWeight 3 L p)) := by gcongr
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
