import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1

/-!
# `RingChartRawD1` from seven short analytic facts (`PartIII-b:C/rep/8/2/1/2`)

Source `the November 2 reference manuscript`
lines 5462, 5466-5476 (chain rule through `(age, phase, trans)`), 2073-2077
(`U_raw = √s[v₁e_r + (v₂+εH)e_z]`, `H = (1-K)ψ`, `K = η∂_η + 2s∂_s`).

The raw ring lift is `axisExt (Nv R b τ)` with `R = ε⁻¹` and `b = bRaw L` the raw profile of the
actual train.  At the chart point `y = (R/√s, 0, η/√s)` (azimuth zero, off the axis):

* `∂_{y₁} = ∂_ρ`, and `∂_ρ(√s b∘chart) = s[∂_q b - ε(b + 2s∂_s b + η∂_η b)]` (`radial_chain`,
  `∂_ρ√s = -εs`, `∂_ρ e_r = 0`);
* `∂_{y₂}` is the hoop derivative: only `∂_φ e_r = e_φ` contributes, `1/ρ = ε√s`, giving
  `ε s b₁ e_φ`;
* `∂_{y₃} = ∂_z`, and `∂_z(√s b∘chart) = s ∂_η b` (`axial_chain`).

Then `b = v + εH e_z` and every difference to the flat derivative carries a factor `ε`, `ε ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

/-- The raw profile `b_raw = (v₁, v₂ + εH)` of the actual train of the level (source 2077). -/
def bRaw (L : ReturnLevel) : ℝ × (ℝ × ℝ) → Merid :=
  UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ

/-- The meridional vector `(m₀, m₁)` as `m₀ e_r + m₁ e_z` at azimuth zero, as a point of `Space`. -/
def merSp (m : Merid) : Space := vecSp ![m 0, 0, m 1]

/-- (S) The raw profile is smooth on the open set `s > 0` (`IsTrain.smooth_v`, `smooth_p`, the
stream `ψ`; existing: `bgRawProfile_eq_on`, `RawProfileSmooth.lean`). -/
def RawProfileSmooth : Prop :=
  ∀ (L : ReturnLevel) (x : ℝ × (ℝ × ℝ)), 0 < x.1 → ContDiffAt ℝ ∞ (bRaw L) x

/-- (A) Off the axis the axis extension has the same first and second Cartesian derivatives
(the axis is closed, so `axisExt f = f` near `y`). -/
def AxisExtPd : Prop :=
  ∀ (f : Space → Space) (y : Space), y ∉ axis →
    (∀ j : Fin 3, physPd (UnforcedLeray.Cons.C03.Concrete.axisExt f) j y = physPd f j y) ∧
    ∀ j l : Fin 3,
      physPd2 (UnforcedLeray.Cons.C03.Concrete.axisExt f) j l y = physPd2 f j l y

/-- (C) The chart point of `(chartTau R p, chartY R p)` is `p`:
`s = R²/ϱ²`, `ξ = Rτ/2 - (R/2) log s`, `η = R y₃/ϱ` at `y = (R/√s, 0, η/√s)`. -/
def ChartId : Prop :=
  ∀ (R : ℝ) (p : Chart), 0 < R → 0 < p.1 →
    chart R (NearInst.chartTau R p) (NearInst.chartY R p) = p

/-- (N0) `∂_{y₁}` of the ring lift at azimuth zero (source 5466-5476; `radial_chain`):
`∂_ρ(Nv R b τ) = s·[∂_q b - ε(b + 2s ∂_s b + η ∂_η b)]` as `e_r, e_z` combination,
`x = chart R τ y`, `s = x.1`, `η = x.2.2`, `ε = R⁻¹`. -/
def NvPd0 : Prop :=
  ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (y : Space), 0 < R → 0 < y 0 → y 1 = 0 →
    DifferentiableAt ℝ b (chart R τ y) →
    physPd (Nv R b τ) 0 y =
      age R y • merSp (UnforcedLeray.Axi.dQ b (chart R τ y) - R⁻¹ • (b (chart R τ y) +
        (2 * age R y) • UnforcedLeray.Axi.dS b (chart R τ y) + trans R y • UnforcedLeray.Axi.dEta b (chart R τ y)))

/-- (N1) `∂_{y₂}` (hoop) of the ring lift at azimuth zero: only `∂_φ e_r = e_φ/ϱ` contributes,
`1/ϱ = ε√s`, giving `ε s b₀ e_φ` (`e_φ = e₂`, index `1` of `Space`). -/
def NvPd1 : Prop :=
  ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (y : Space), 0 < R → 0 < y 0 → y 1 = 0 →
    DifferentiableAt ℝ b (chart R τ y) →
    physPd (Nv R b τ) 1 y = vecSp ![0, R⁻¹ * age R y * b (chart R τ y) 0, 0]

/-- (N2) `∂_{y₃}` of the ring lift (`axial_chain`): `s · ∂_η b` as `e_r, e_z` combination. -/
def NvPd2 : Prop :=
  ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (y : Space), 0 < R → 0 < y 0 → y 1 = 0 →
    DifferentiableAt ℝ b (chart R τ y) →
    physPd (Nv R b τ) 2 y = age R y • merSp (UnforcedLeray.Axi.dEta b (chart R τ y))

/-- (B0) Bound for `j = 0`: with `b = v + εH e_z`,
`s[∂_q b - ε(b + 2s∂_s b + η∂_η b)] - s ∂_q v = s ε[∂_q H e_z - (b + K b)]`, of size
`≤ C ε s 𝔴₃` for `ε ≤ 1` (`v`: orders ≤ 1, `ψ`: orders ≤ 3, `η`-power ≤ 2; `s∂_s = ∂_σ`). -/
def RawD1Bound0 : Prop :=
  ∃ C : ℝ, ∀ (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    ‖p.1 • merSp (UnforcedLeray.Axi.dQ (bRaw L) p - L.ε • (bRaw L p + (2 * p.1) • UnforcedLeray.Axi.dS (bRaw L) p +
        p.2.2 • UnforcedLeray.Axi.dEta (bRaw L) p)) - p.1 • vecSp (flatD1 L p.1 p.2 0)‖ ≤
      C * L.ε * p.1 * trainWeight 3 L p

/-- (B1) Bound for `j = 1`: `|ε s b₀| = ε s |v₁| ≤ ε s 𝔴₃` and `flatD1 · · 1 = 0`. -/
def RawD1Bound1 : Prop :=
  ∃ C : ℝ, ∀ (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    ‖vecSp ![0, L.ε * p.1 * bRaw L p 0, 0] - p.1 • vecSp (flatD1 L p.1 p.2 1)‖ ≤
      C * L.ε * p.1 * trainWeight 3 L p

/-- (B2) Bound for `j = 2`: `s ∂_η b - s ∂_η v = s ε ∂_η H e_z`, `∂_ηH = -η ψ_ηη - 2sψ_sη`. -/
def RawD1Bound2 : Prop :=
  ∃ C : ℝ, ∀ (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    ‖p.1 • merSp (UnforcedLeray.Axi.dEta (bRaw L) p) - p.1 • vecSp (flatD1 L p.1 p.2 2)‖ ≤
      C * L.ε * p.1 * trainWeight 3 L p

theorem ringChartRawD1_of (hS : RawProfileSmooth) (hA : AxisExtPd) (hC : ChartId)
    (n0 : NvPd0) (n1 : NvPd1) (n2 : NvPd2)
    (b0 : RawD1Bound0) (b1 : RawD1Bound1) (b2 : RawD1Bound2) : RingChartRawD1 := by
  obtain ⟨C0, H0⟩ := b0
  obtain ⟨C1, H1⟩ := b1
  obtain ⟨C2, H2⟩ := b2
  refine ⟨max (max C0 C1) C2, fun Pl L hε p hp0 _ j => ?_⟩
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp0
  have hch := hC L.ε⁻¹ p hR hp0
  have hage : age L.ε⁻¹ (NearInst.chartY L.ε⁻¹ p) = p.1 := by
    exact congrArg Prod.fst hch
  have htr : trans L.ε⁻¹ (NearInst.chartY L.ε⁻¹ p) = p.2.2 := by
    exact congrArg (fun q => q.2.2) hch
  have hy0 : 0 < (NearInst.chartY L.ε⁻¹ p) 0 := by
    simp only [NearInst.chartY]
    exact div_pos hR hs
  have hy1 : (NearInst.chartY L.ε⁻¹ p) 1 = 0 := by simp [NearInst.chartY]
  have hax : NearInst.chartY L.ε⁻¹ p ∉ axis := by
    intro h
    exact hy0.ne' h.1
  have hdiff : DifferentiableAt ℝ (bRaw L) (chart L.ε⁻¹ (NearInst.chartTau L.ε⁻¹ p)
      (NearInst.chartY L.ε⁻¹ p)) := by
    rw [hch]
    exact (hS L p hp0).differentiableAt (by simp)
  have hnn : 0 ≤ L.ε * p.1 * trainWeight 3 L p := by
    have := trainWeight_nonneg 3 L p
    have := L.ε_pos
    positivity
  have hm0 : C0 ≤ max (max C0 C1) C2 := (le_max_left _ _).trans (le_max_left _ _)
  have hm1 : C1 ≤ max (max C0 C1) C2 := (le_max_right _ _).trans (le_max_left _ _)
  have hm2 : C2 ≤ max (max C0 C1) C2 := le_max_right _ _
  have hext : ∀ j : Fin 3, physPd (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) j
      (NearInst.chartY L.ε⁻¹ p) =
      physPd (Nv L.ε⁻¹ (bRaw L) (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) :=
    fun j => (hA (Nv L.ε⁻¹ (bRaw L) (NearInst.chartTau L.ε⁻¹ p)) _ hax).1 j
  fin_cases j
  · show ‖physPd (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) 0 (NearInst.chartY L.ε⁻¹ p) -
      p.1 • vecSp (flatD1 L p.1 p.2 0)‖ ≤ _
    rw [hext _, n0 _ _ _ _ hR hy0 hy1 hdiff, hch, hage, htr, inv_inv]
    refine (H0 L hε p hp0).trans ?_
    simp only [pow_zero, mul_one]
    nlinarith
  · show ‖physPd (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) 1 (NearInst.chartY L.ε⁻¹ p) -
      p.1 • vecSp (flatD1 L p.1 p.2 1)‖ ≤ _
    rw [hext _, n1 _ _ _ _ hR hy0 hy1 hdiff, hch, hage, inv_inv]
    refine (H1 L hε p hp0).trans ?_
    simp only [pow_zero, mul_one]
    nlinarith
  · show ‖physPd (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) 2 (NearInst.chartY L.ε⁻¹ p) -
      p.1 • vecSp (flatD1 L p.1 p.2 2)‖ ≤ _
    rw [hext _, n2 _ _ _ _ hR hy0 hy1 hdiff, hch, hage]
    refine (H2 L hε p hp0).trans ?_
    simp only [pow_zero, mul_one]
    nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
