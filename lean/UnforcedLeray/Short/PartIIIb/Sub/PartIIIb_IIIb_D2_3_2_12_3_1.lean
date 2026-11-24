import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1` (`StrChartBound`): decomposition

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

`StrChartBound` follows from the Cauchy-Schwarz core `StressCSRegion` (stated for an explicit support
radius `Y` of `Φ` and `R = ε⁻¹`, `P = 2c/R`).  The core is proved from three leaves:
`StrPhysAbsLe` (pointwise bound of the physical tensor), `ChartOfMemStrRegion` (the ball
`{|z₃| ≤ Y}` is mapped into `StrRegion Y`), and `RingChartRegionLintegral` (change of variables
`Axi.phaseAvg_ringChart` expressed for `chartOf`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- **Leaf 1** (source 2683): `|𝒩_T g| ≤ s Σ_{ab} |nsSym g_{ab}|` entrywise, `s = R²/ϱ²`
(`cylFrame` entries are bounded by `1`: `|z 0| ≤ ϱ`, `|z 1| ≤ ϱ`; the factor `s ≥ 0`). -/
def StrPhysAbsLe : Prop :=
  ∀ (R c : ℝ) (g : Chart → Ten3) (x : ℝ × Space) (i j : Fin 3),
    |strPhys R c g x i j| ≤ (NearInst.chartOf R c x.2 x.1).1 *
      ∑ a : Fin 3, ∑ b : Fin 3, |NearInst.nsSym (g (NearInst.chartOf R c x.2 x.1)) a b|

/-- **Leaf 2** (source 2696): `|R z₃/ϱ| ≤ Y √(1 + R²/ϱ²)` when `|z₃| ≤ Y` (because
`R/ϱ ≤ √(1 + R²/ϱ²)`; for `ϱ = 0` the left side is `0`). -/
def ChartOfMemStrRegion : Prop :=
  ∀ (R Y c : ℝ), 0 < R → 0 ≤ Y → ∀ (z : Space) (τ : ℝ), |z 2| ≤ Y →
    NearInst.chartOf R c z τ ∈ StrRegion Y

/-- **Leaf 3** (source 2683, 3256-3268): `Axi.phaseAvg_ringChart` for the chart composite
`x ↦ G (chartOf R c x.2 x.1)` on the phase cell (`chartOf` agrees a.e. with
`(age, phase, trans)`, `NearInst.chartOf_eq_ring`; `Ioc 0 P ×ˢ univ` is the Tonelli
product; the factor `ofReal P` undoes the normalisation `P⁻¹`). -/
def RingChartRegionLintegral : Prop :=
  ∀ (R c P : ℝ), 0 < R → 0 < c → P = 2 * c / R → ∀ G : Chart → ℝ≥0∞, Measurable G →
    (∀ s q η, G (s, (q + c, η)) = G (s, (q, η))) →
    ∫⁻ x in phaseCell P, G (NearInst.chartOf R c x.2 x.1) =
      ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p

/-- **Core** (source 2698-2700, 4284-4286): Cauchy-Schwarz on the phase cell with weight `s^{-1/2}`
for the stress pairing against a phase test supported in `‖y‖ ≤ Y`.  Uses `StrPhysAbsLe`,
`ChartOfMemStrRegion`, `RingChartRegionLintegral` with
`G = 1_{StrRegion Y} · s² ‖g‖ₑ²` (periodic in `q`), `s² · s^{-5/2} = s^{-1/2}`, and
`|dy j Φ|` bounded on the support (smooth, compactly supported). -/
def StressCSRegion : Prop :=
  ∀ (R c P Y : ℝ) (Φ : ℝ × Space → CVec3), 0 < R → 0 < c → P = 2 * c / R → 0 ≤ Y →
    IsPhaseTest P Φ → (∀ τ y, Y < ‖y‖ → Φ (τ, y) = 0) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Chart → Ten3, Measurable g →
      (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) < ⊤ →
      Integrable (fun x : ℝ × Space => ∑ i : Fin 3, ∑ j : Fin 3,
          ((strPhys R c g x i j : ℝ) : ℂ) * dy j Φ x i) (volume.restrict (phaseCell P)) ∧
      ‖stressPair P (strPhys R c g) Φ‖ ≤
        K * ((∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ)).toReal

theorem strChartBound_proved_of (h : StressCSRegion) : StrChartBound := by
  intro c ε hc hε Φ hΦ
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hY : ∀ τ y, max R 0 < ‖y‖ → Φ (τ, y) = 0 :=
    fun τ y hy => hR τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  obtain ⟨K, hK0, hK⟩ := h ε⁻¹ c (2 * ε * c) (max R 0) Φ (inv_pos.2 hε) hc
    (by field_simp) (le_max_right _ _) hΦ hY
  exact ⟨max R 0, K, hK0, hK⟩

end UnforcedLeray.Short.PartIIIb.Concrete
