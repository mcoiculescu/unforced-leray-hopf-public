import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_5
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicRepresentative
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.LocInt

/-!
# Helper for `PartII-b:G4/3/5/1` (`ProfileWindowZero`): the chart integral of `√s b_j`

Source of record: `the November 2 reference manuscript`, lines 1902-1906, 2370-2384.

The glue of `chartWindowIntegral_of` (`Sub/PartII-b_T09_4_2.lean`), with `gDiv` replaced by a generic
`g` that has a periodic representative and is locally integrable on `s > 0`; applied to
`g = √s b_j`, `b ∈ H_p`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- Generic window chart integral (the glue of `chartWindowIntegral_of`). -/
theorem windowChartIntegralGen (c ε : ℝ) (χ : Coord → ℝ) (φ : ℝ × Space → ℂ) (g : Coord → ℂ)
    (hc : 0 < c) (hε : 0 < ε) (hχ : IsWinTest c χ)
    (hrep : ∃ (g' : Coord → ℂ) (M : Set Coord), Measurable g' ∧
      (∀ s ξ η : ℝ, g' (s, (ξ + c, η)) = g' (s, (ξ, η))) ∧
      MeasurableSet M ∧ volume M = 0 ∧
      (∀ s ξ η : ℝ, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) ∧
      ∀ x : Coord, 0 < x.1 → x ∉ M → g x = g' x)
    (hloc : LocallyIntegrableOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume)
    (hφ : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      φ (τ, y) = ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ)) :
    phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ g x) =
      ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) * wInt χ g := by
  obtain ⟨hWm, hWper, _hWcell⟩ := winPerFacts c χ hc hχ
  obtain ⟨g', M, hg'm, hg'per, hMm, hM0, hMper, hgg'⟩ := hrep
  set F : Coord → ℂ := fun x => ((winPer c χ x : ℝ) : ℂ) * g' x with hF
  have hFm : Measurable F := (Complex.measurable_ofReal.comp hWm).mul hg'm
  have hFper : ∀ s ξ η : ℝ, F (s, (ξ + c, η)) = F (s, (ξ, η)) := by
    intro s ξ η
    simp only [hF, hWper, hg'per]
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hae : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)),
      ((winPer c χ p : ℝ) : ℂ) * g p = F p := by
    have hnull : ∀ᵐ p ∂(volume : Measure Coord), p ∉ M := measure_eq_zero_iff_ae_notMem.1 hM0
    filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem hS] with p hpM hp
    simp only [hF]
    rw [hgg' p hp.1 hpM]
  have hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖F p‖ₑ < ⊤ := by
    have := winFinite c χ g hc hχ hloc
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) this
    filter_upwards [hae] with p hp
    rw [hp]
  have hbr := ringBridgeC c ε F hc hε hFm hFper hfin
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  have hpull := chartNullPullback ε⁻¹ c (2 * ε * c) hR hc hP M hMm hM0 hMper
  have hax : ∀ᵐ y : Space, y ∉ Axi.axis := measure_eq_zero_iff_ae_notMem.1 Axi.volume_axis
  have hinner : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ∫ y : Space, φ (τ, y) * sLift ε⁻¹ g (τ, y) =
        ∫ y : Space, F (Axi.chart ε⁻¹ τ y) := by
    filter_upwards [hpull] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ, hax] with y hy hya
    show φ (τ, y) * g (Axi.chart ε⁻¹ τ y) = F (Axi.chart ε⁻¹ τ y)
    rw [hφ τ y hya, hgg' _ (Axi.age_pos hR.ne' hya) hy]
  unfold phaseInt
  rw [integral_congr_ae hinner, hbr, winIntCell c χ _ hc hχ]
  congr 1
  refine setIntegral_congr_ae hS ?_
  filter_upwards [(ae_restrict_iff' hS).1 hae] with p hp hpm
  rw [hp hpm]

/-- **`WZ-B` leaf**: `√s b_j` has a periodic representative. -/
theorem hrSqrtPeriodicRep (c : ℝ) (b : CProf) (j : Fin 2) (hc : 0 < c) (hb : InHr c bgp b) :
    ∃ (g' : Coord → ℂ) (M : Set Coord), Measurable g' ∧
      (∀ s ξ η : ℝ, g' (s, (ξ + c, η)) = g' (s, (ξ, η))) ∧
      MeasurableSet M ∧ volume M = 0 ∧
      (∀ s ξ η : ℝ, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) ∧
      ∀ x : Coord, 0 < x.1 → x ∉ M → ((Real.sqrt x.1 : ℝ) : ℂ) * b x j = g' x := by
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hMper, hbb'⟩ :=
    periodicRepresentative c bgp hc b hb.periodic hb.meas
  have hev : Measurable fun x => b' x j :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) j).measurable.comp hb'm
  refine ⟨fun x => ((Real.sqrt x.1 : ℝ) : ℂ) * b' x j, M,
    (Complex.measurable_ofReal.comp measurable_fst.sqrt).mul hev, ?_, hMm, hM0, hMper, ?_⟩
  · intro s ξ η
    simp only [hb'per s ξ η]
  · intro x hx hxM
    simp only [hbb' x hx hxM]

/-- **`WZ-B`**: the chart integral of `√s b_j` against a window phase test. -/
theorem windowChartIntegralVec (c ε : ℝ) (χ : Coord → ℝ) (φ : ℝ × Space → ℂ) (b : CProf)
    (j : Fin 2) (hc : 0 < c) (hε : 0 < ε) (hχ : IsWinTest c χ) (hb : InHr c bgp b)
    (hφ : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      φ (τ, y) = ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ)) :
    phaseInt (2 * ε * c)
        (fun x => φ x * sLift ε⁻¹ (fun z : Coord => ((Real.sqrt z.1 : ℝ) : ℂ) * b z j) x) =
      ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) *
        wInt χ (fun z : Coord => ((Real.sqrt z.1 : ℝ) : ℂ) * b z j) :=
  windowChartIntegralGen c ε χ φ _ hc hε hχ (hrSqrtPeriodicRep c b j hc hb)
    (profileLocInt c b hc hb j) hφ

end UnforcedLeray.Short.IIb
