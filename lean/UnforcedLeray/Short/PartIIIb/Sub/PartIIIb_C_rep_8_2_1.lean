import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org

/-!
# `RingChartRules` from the four ring-chart expansions (`PartIII-b:C/rep/8/2/1`)

Source `the November 2 reference manuscript`
lines 5460-5465 (exact ring-chart rules), 2073-2077 (ring lift `U_raw = √s[v₁e_r + (v₂+εH)e_z]`,
`H = (1-K)ψ`), 1217 (`p_raw = a_r² p`).

The four conjuncts of `RingChartRulesAt` are stated as universal chart-point estimates, uniform in
the level (only `ε ≤ 1` is used; every error term carries a factor `ε` and at most three
`(σ,q,η)`-derivatives, `σ = log s`, of `v, p, ψ`), with `k = 0` (no `ν⁻¹` loss).
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- (i) `U_raw - √s v = √s·ε·H·e_z`, `|H| ≤ 3·𝔴₃` (source 2073-2077, 5460-5461, 5464-5465). -/
def RingChartRawVal : Prop :=
  ∃ C : ℝ, ∀ (Pl : PlanarData) (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    p.1 ≤ 1 / L.ν →
    ‖rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) -
        Real.sqrt p.1 • vecSp (emb (trainV L p.1 p.2))‖ ≤
      C * L.ν⁻¹ ^ 0 * L.ε * Real.sqrt p.1 * trainWeight 3 L p

/-- (ii) `D U_raw = s(D_flat v + εC₁)`: chain rule through `(age, phase, trans)`, with
`∂_ϱ s = -2εs^{3/2}`, `∂_ϱξ = √s`, `∂_ϱη = -εη√s`, `∂_{y₃}η = √s`, hoop `∂_{y₂}e_r = e_φ/ϱ`,
`1/ϱ = ε√s` (source 5462, 5466-5476). -/
def RingChartRawD1 : Prop :=
  ∃ C : ℝ, ∀ (Pl : PlanarData) (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    p.1 ≤ 1 / L.ν → ∀ j : Fin 3,
    ‖physPd (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) -
        p.1 • vecSp (flatD1 L p.1 p.2 j)‖ ≤ C * L.ν⁻¹ ^ 0 * L.ε * p.1 * trainWeight 3 L p

/-- (iii) `D² U_raw = s^{3/2}(D²_flat v + εC₂)` (source 5463, 5466-5476). -/
def RingChartRawD2 : Prop :=
  ∃ C : ℝ, ∀ (Pl : PlanarData) (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    p.1 ≤ 1 / L.ν → ∀ j l : Fin 3,
    ‖physPd2 (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) j l (NearInst.chartY L.ε⁻¹ p) -
        p.1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L p.1 p.2 j l)‖ ≤
      C * L.ν⁻¹ ^ 0 * L.ε * p.1 ^ (3 / 2 : ℝ) * trainWeight 3 L p

/-- (iv) `∇p_lift = s^{3/2}(∇_flat p_cyl + εC₃)`, `∇(s p_cyl) = s^{3/2}(∂_qp,0,∂_ηp) +
εs^{3/2}(-2p - η∂_ηp - 2s∂_sp)e₁` (source 1217, 5465, 5272-5282). -/
def RingChartLiftGrad : Prop :=
  ∃ C : ℝ, ∀ (Pl : PlanarData) (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 →
    p.1 ≤ 1 / L.ν →
    ‖physGrad (liftP L (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) -
        p.1 ^ (3 / 2 : ℝ) • vecSp (emb (mgrad (trainP L p.1) p.2))‖ ≤
      C * L.ν⁻¹ ^ 0 * L.ε * p.1 ^ (3 / 2 : ℝ) * trainWeight 3 L p

theorem ringChartRules_of (h1 : RingChartRawVal) (h2 : RingChartRawD1) (h3 : RingChartRawD2)
    (h4 : RingChartLiftGrad) (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.RingChartRules := by
  obtain ⟨C1, H1⟩ := h1
  obtain ⟨C2, H2⟩ := h2
  obtain ⟨C3, H3⟩ := h3
  obtain ⟨C4, H4⟩ := h4
  have hev := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨max (max C1 C2) (max C3 C4), 0, ?_⟩
  filter_upwards [hev] with n hn p hp0 hp1
  have hε : (D.level n).ε ≤ 1 := hn.2
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε0 : 0 < (D.level n).ε := (D.level n).ε_pos
  have hw := trainWeight_nonneg 3 (D.level n) p
  have hs : 0 < p.1 := hp0
  have hsq : 0 ≤ Real.sqrt p.1 := Real.sqrt_nonneg _
  have hs32 : 0 ≤ p.1 ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have hm1 : C1 ≤ max (max C1 C2) (max C3 C4) := (le_max_left _ _).trans (le_max_left _ _)
  have hm2 : C2 ≤ max (max C1 C2) (max C3 C4) := (le_max_right _ _).trans (le_max_left _ _)
  have hm3 : C3 ≤ max (max C1 C2) (max C3 C4) := (le_max_left _ _).trans (le_max_right _ _)
  have hm4 : C4 ≤ max (max C1 C2) (max C3 C4) := (le_max_right _ _).trans (le_max_right _ _)
  have hpos : ∀ x : ℝ, 0 ≤ x → ∀ C C' : ℝ, C ≤ C' →
      C * (D.level n).ν⁻¹ ^ 0 * (D.level n).ε * x * trainWeight 3 (D.level n) p ≤
      C' * (D.level n).ν⁻¹ ^ 0 * (D.level n).ε * x * trainWeight 3 (D.level n) p := by
    intro x hx C C' hC
    have : 0 ≤ (D.level n).ε * x * trainWeight 3 (D.level n) p := by positivity
    simp only [pow_zero, mul_one]
    nlinarith
  refine ⟨(H1 D.Pl (D.level n) hε p hp0 hp1).trans (hpos _ hsq _ _ hm1), fun j => ?_,
    fun j l => ?_, ?_⟩
  · exact (H2 D.Pl (D.level n) hε p hp0 hp1 j).trans (hpos _ hs.le _ _ hm2)
  · exact (H3 D.Pl (D.level n) hε p hp0 hp1 j l).trans (hpos _ hs32 _ _ hm3)
  · exact (H4 D.Pl (D.level n) hε p hp0 hp1).trans (hpos _ hs32 _ _ hm4)

end UnforcedLeray.Short.PartIIIb.Concrete
