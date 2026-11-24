import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull

/-!
# Part II-b, task `PartII-b:T09/4/2` (`ChartWindowIntegral`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

`ChartWindowIntegral` is the identity `⟪φ, sLift gDiv⟫ = (πR²/c) ∫ χ s^{-5/2} gDiv`, `R = ε⁻¹`,
for a phase test `φ` that is the chart pullback of a window test `χ`.  Route:

1. `gDiv` has an everywhere `c`-periodic measurable representative `g'` off a periodic null set `M`
   (`GDivPeriodicRep`); `chartNullPullback` makes `chart τ y ∉ M` for a.e. `(τ, y)`, and `y ∉ axis`
   gives `φ(τ, y) = winPer χ (chart τ y)` and `s > 0`; hence the phase integrand is a.e.
   `F (chart τ y)` with `F = winPer χ · g'`, measurable and `c`-periodic (`WinPerFacts`).
2. `F` is integrable against the cell weight (`WinFinite`, from `DivLocInt`).
3. The bridge `RingBridgeC` (`Axi.phaseAvg_ringChart` for the four nonnegative parts, in three
   stages `RingBridgeNN`, `RingBridgeReal`, `RingBridgeC`) turns the phase integral of `F ∘ chart`
   into `(πR²/c) ∫_{s>0, cell} s^{-5/2} F`.
4. `WinIntCell`: `wInt χ g = ∫_{s>0, cell} s^{-5/2} winPer χ · g` (the integrand of `wInt` vanishes
   off `s > 0`, `|q| < c/2`, where `winPer χ = χ`).

Proved here: `chartWindowIntegral_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- **Leaf `T09/4/2/1`** (SP 1912-1918): for a window test, `winPer c χ` is measurable (`χ`
continuous, the floor is measurable), `c`-periodic in `q`, and equals `χ` on the cell
`q ∈ [-c/2, c/2)`. -/
def WinPerFacts : Prop :=
  ∀ (c : ℝ) (χ : Coord → ℝ), 0 < c → IsWinTest c χ →
    Measurable (winPer c χ) ∧
    (∀ s ξ η : ℝ, winPer c χ (s, (ξ + c, η)) = winPer c χ (s, (ξ, η))) ∧
    (∀ x : Coord, x.2.1 ∈ Ico (-c / 2) (c / 2) → winPer c χ x = χ x)

/-- **Leaf `T09/4/2/2`** (as in `pairCont_rep`, from `periodicRepresentative` of
`Tasks/NvCNorm/PeriodicRepresentative.lean`): for `DivData`, `gDiv` agrees on `s > 0`, off a
measurable `q`-periodic null set `M`, with a measurable everywhere `q`-periodic function `g'`.
(`gDiv = s (Qb₀ + ε b₀ + Eb₁)`; `b`, `√s Qb`, `√s Eb ∈ H_r` are a.e. `q`-periodic and measurable;
apply `periodicRepresentative` to the three profiles and reassemble on `s > 0`.) -/
def GDivPeriodicRep : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    ∃ (g' : Coord → ℂ) (M : Set Coord), Measurable g' ∧
      (∀ s ξ η : ℝ, g' (s, (ξ + c, η)) = g' (s, (ξ, η))) ∧
      MeasurableSet M ∧ volume M = 0 ∧
      (∀ s ξ η : ℝ, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) ∧
      ∀ x : Coord, 0 < x.1 → x ∉ M → gDiv ε b Qb Eb x = g' x

/-- **Leaf `T09/4/2/3`**: a window test times a locally integrable function (on `s > 0`) is
integrable against the cell weight: `χ` is bounded with compact support in `s > 0`, `winPer = χ`
on the cell. -/
def WinFinite : Prop :=
  ∀ (c : ℝ) (χ : Coord → ℝ) (g : Coord → ℂ), 0 < c → IsWinTest c χ →
    LocallyIntegrableOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume →
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖((winPer c χ p : ℝ) : ℂ) * g p‖ₑ < ⊤

/-- **Leaf `T09/4/2/4`** (`Axi.phaseAvg_ringChart`, `RingMeasure.lean:229`, with `R = ε⁻¹`,
`P = 2εc = 2c/R`): the ring-chart average of a nonnegative measurable `c`-periodic function, as a
real Bochner identity, when the weighted cell integral is finite (both sides equal the `toReal` of
the `ENNReal` identity; `integral_eq_lintegral_of_nonneg_ae`). -/
def RingBridgeNN : Prop :=
  ∀ (c ε : ℝ) (G : Coord → ℝ), 0 < c → 0 < ε → Measurable G → (∀ x, 0 ≤ G x) →
    (∀ s ξ η : ℝ, G (s, (ξ + c, η)) = G (s, (ξ, η))) →
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G p) < ⊤ →
    (2 * ε * c)⁻¹ * ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, G (Axi.chart ε⁻¹ τ y) =
      Real.pi * (ε⁻¹) ^ 2 / c *
        ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * G p

/-- **Leaf `T09/4/2/5`**: the same for a signed real measurable `c`-periodic `G` with
`∫⁻ weight · ‖G‖ₑ < ⊤` (split `G = G⁺ - G⁻`, apply `RingBridgeNN`; for a.e. `τ` the inner `y`-integral
is finite, so the Bochner integral splits). -/
def RingBridgeReal : Prop :=
  ∀ (c ε : ℝ) (G : Coord → ℝ), 0 < c → 0 < ε → Measurable G →
    (∀ s ξ η : ℝ, G (s, (ξ + c, η)) = G (s, (ξ, η))) →
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖G p‖ₑ < ⊤ →
    (2 * ε * c)⁻¹ * ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, G (Axi.chart ε⁻¹ τ y) =
      Real.pi * (ε⁻¹) ^ 2 / c *
        ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * G p

/-- **Leaf `T09/4/2/6`**: the complex version, as used in the glue (real and imaginary parts, with
`‖re F‖ₑ, ‖im F‖ₑ ≤ ‖F‖ₑ`; `integral_re`, `integral_im` on the inner and outer integrals). -/
def RingBridgeC : Prop :=
  ∀ (c ε : ℝ) (F : Coord → ℂ), 0 < c → 0 < ε → Measurable F →
    (∀ s ξ η : ℝ, F (s, (ξ + c, η)) = F (s, (ξ, η))) →
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖F p‖ₑ < ⊤ →
    ((2 * ε * c)⁻¹ : ℝ) • ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, F (Axi.chart ε⁻¹ τ y) =
      ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) *
        ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F p

/-- **Leaf `T09/4/2/7`**: the window pairing is the cell integral: the integrand of `wInt χ g`
vanishes off `{s > 0, |q| < c/2}` (`tsupport χ`), and on the cell `winPer χ = χ`. -/
def WinIntCell : Prop :=
  ∀ (c : ℝ) (χ : Coord → ℝ) (g : Coord → ℂ), 0 < c → IsWinTest c χ →
    wInt χ g = ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (((winPer c χ p : ℝ) : ℂ) * g p)

/-- **Glue** (`PartII-b:T09/4/2`): `ChartWindowIntegral` from the leaves. -/
theorem chartWindowIntegral_of (h1 : WinPerFacts) (h2 : GDivPeriodicRep) (h3 : DivLocInt)
    (h4 : WinFinite) (h6 : RingBridgeC) (h7 : WinIntCell) : ChartWindowIntegral := by
  intro c ε r b Qb Eb χ φ hc hε hr hd hχ hφ
  obtain ⟨hWm, hWper, _hWcell⟩ := h1 c χ hc hχ
  obtain ⟨g', M, hg'm, hg'per, hMm, hM0, hMper, hgg'⟩ := h2 c ε r b Qb Eb hc hε hr hd
  set F : Coord → ℂ := fun x => ((winPer c χ x : ℝ) : ℂ) * g' x with hF
  have hFm : Measurable F := (Complex.measurable_ofReal.comp hWm).mul hg'm
  have hFper : ∀ s ξ η : ℝ, F (s, (ξ + c, η)) = F (s, (ξ, η)) := by
    intro s ξ η
    simp only [hF, hWper, hg'per]
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hae : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)),
      ((winPer c χ p : ℝ) : ℂ) * gDiv ε b Qb Eb p = F p := by
    have hnull : ∀ᵐ p ∂(volume : Measure Coord), p ∉ M := measure_eq_zero_iff_ae_notMem.1 hM0
    filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem hS] with p hpM hp
    simp only [hF]
    rw [hgg' p hp.1 hpM]
  have hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖F p‖ₑ < ⊤ := by
    have := h4 c χ (gDiv ε b Qb Eb) hc hχ (h3 c ε r b Qb Eb hc hε hr hd)
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) this
    filter_upwards [hae] with p hp
    rw [hp]
  have hbr := h6 c ε F hc hε hFm hFper hfin
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  have hpull := chartNullPullback ε⁻¹ c (2 * ε * c) hR hc hP M hMm hM0 hMper
  have hax : ∀ᵐ y : Space, y ∉ Axi.axis := measure_eq_zero_iff_ae_notMem.1 Axi.volume_axis
  have hinner : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ∫ y : Space, φ (τ, y) * sLift ε⁻¹ (gDiv ε b Qb Eb) (τ, y) =
        ∫ y : Space, F (Axi.chart ε⁻¹ τ y) := by
    filter_upwards [hpull] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ, hax] with y hy hya
    show φ (τ, y) * gDiv ε b Qb Eb (Axi.chart ε⁻¹ τ y) = F (Axi.chart ε⁻¹ τ y)
    rw [hφ τ y hya, hgg' _ (Axi.age_pos hR.ne' hya) hy]
  unfold phaseInt
  rw [integral_congr_ae hinner, hbr, h7 c χ _ hc hχ]
  congr 1
  refine setIntegral_congr_ae hS ?_
  filter_upwards [(ae_restrict_iff' hS).1 hae] with p hp hpm
  rw [hp hpm]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.chartWindowIntegral_of
