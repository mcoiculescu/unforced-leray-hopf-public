import UnforcedLeray.Short.PartIIa.Sub.N02_4_10

/-!
# Part II-a, task `PartII-a:N02/4/10/5` (`NtmMeasureMono`): monotone moments on the cell

Target: `ntmMeasureMono : NtmMeasureMono` (`Sub/N02_4_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

Outline. For a smooth band-supported test `g` the moment integrand
`p ↦ (|η|^j)^2 ‖g p‖^2` is integrated against `measureH c = s^{-3/2} ds dq dη` on the cell
`Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`. The monotone steps are done with `lintegral`, which needs no
integrability: Tonelli on the cell (`s` outermost, then `η`, then `q`), the `q`-integral is the
interval integral of the hypothesis, and the compact band gives finiteness of the outer
`lintegral` for the larger test, which lets `ENNReal.toReal_mono` return to Bochner integrals.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Tonelli on the profile cell, with `s` outermost, then `η`, then `q` innermost. -/
theorem mm_lintegral_cell_iter (c : ℝ) {Φ : Profile → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ p in cell c, Φ p = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η, ∫⁻ q in Ioc 0 c, Φ (s, q, η) := by
  have hcell : cell c = Ioi (0 : ℝ) ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)) := rfl
  rw [hcell, Measure.volume_eq_prod, setLIntegral_prod _ hΦ.aemeasurable]
  refine lintegral_congr fun s => ?_
  try dsimp only
  have e : (volume : Measure (ℝ × ℝ)).restrict (Ioc 0 c ×ˢ (univ : Set ℝ))
      = (volume.restrict (Ioc 0 c)).prod (volume.restrict (univ : Set ℝ)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hf : Measurable fun y : ℝ × ℝ => Φ (s, y) :=
    hΦ.comp (measurable_const.prodMk measurable_id)
  rw [e, lintegral_prod_symm _ hf.aemeasurable, Measure.restrict_univ]

/-- The `q`-integral of one cell slice of the moment integrand. -/
theorem mm_inner (c : ℝ) (g : Profile → MeridC) (hgc : Continuous g) (j : ℕ) (s η : ℝ) :
    ∫⁻ q in Ioc 0 c, weightH (s, q, η) * ENNReal.ofReal ((|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2)
      = ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal ((|η| ^ j) ^ 2)
          * ENNReal.ofReal (∫ q in Ioc 0 c, ‖g (s, q, η)‖ ^ 2) := by
  have hw : ∀ q : ℝ, weightH (s, q, η) * ENNReal.ofReal ((|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2)
      = (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal ((|η| ^ j) ^ 2))
          * ENNReal.ofReal (‖g (s, q, η)‖ ^ 2) := by
    intro q
    show ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal ((|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2) = _
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (|η| ^ j) ^ 2 by positivity)]
    ring
  have hsqc : Continuous fun q : ℝ => ‖g (s, q, η)‖ ^ 2 := by fun_prop
  have hsqm : Measurable fun q : ℝ => ENNReal.ofReal (‖g (s, q, η)‖ ^ 2) :=
    hsqc.measurable.ennreal_ofReal
  have hsqi : IntegrableOn (fun q : ℝ => ‖g (s, q, η)‖ ^ 2) (Ioc 0 c) :=
    hsqc.integrableOn_Ioc
  have hsqnn : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] fun q : ℝ => ‖g (s, q, η)‖ ^ 2 :=
    ae_of_all _ fun q => by positivity
  calc ∫⁻ q in Ioc 0 c, weightH (s, q, η) * ENNReal.ofReal ((|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2)
      = ∫⁻ q in Ioc 0 c, (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal ((|η| ^ j) ^ 2))
          * ENNReal.ofReal (‖g (s, q, η)‖ ^ 2) := lintegral_congr hw
    _ = (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal ((|η| ^ j) ^ 2))
          * ∫⁻ q in Ioc 0 c, ENNReal.ofReal (‖g (s, q, η)‖ ^ 2) :=
        lintegral_const_mul _ hsqm
    _ = ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal ((|η| ^ j) ^ 2)
          * ENNReal.ofReal (∫ q in Ioc 0 c, ‖g (s, q, η)‖ ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hsqi hsqnn]

/-- The moment `lintegral` over `measureH c` as an iterated integral over `s`, then `η`. -/
theorem mm_lint_eq (c : ℝ) (g : Profile → MeridC) (hgc : Continuous g) (j : ℕ) :
    ∫⁻ p, ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2) ∂measureH c
      = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
          * ENNReal.ofReal ((|η| ^ j) ^ 2) * ENNReal.ofReal (∫ q in Ioc 0 c, ‖g (s, q, η)‖ ^ 2) := by
  have hFc : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2 := by fun_prop
  have hFm : Measurable fun p : Profile => ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2) :=
    hFc.measurable.ennreal_ofReal
  have hΦ : Measurable fun p : Profile =>
      weightH p * ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2) :=
    measurable_weightH.mul hFm
  calc ∫⁻ p, ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2) ∂measureH c
      = ∫⁻ p in cell c, weightH p * ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2) :=
        lintegral_withDensity_eq_lintegral_mul (cellMeasure c) measurable_weightH hFm
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η, ∫⁻ q in Ioc 0 c,
          weightH (s, q, η) * ENNReal.ofReal ((|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2) :=
        mm_lintegral_cell_iter c hΦ
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
          * ENNReal.ofReal ((|η| ^ j) ^ 2) * ENNReal.ofReal (∫ q in Ioc 0 c, ‖g (s, q, η)‖ ^ 2) := by
        refine lintegral_congr fun s => lintegral_congr fun η => ?_
        exact mm_inner c g hgc j s η

theorem ntmMeasureMono : NtmMeasureMono := by
  intro c hc g₁ g₂ hg₁ hg₂ hle j
  have hcont₁ : Continuous g₁ := hg₁.smooth.continuous
  have hcont₂ : Continuous g₂ := hg₂.smooth.continuous
  -- finiteness of the lintegral of the larger moment, from the compact band of `g₂`
  obtain ⟨s0, s1, L, hs0, hb⟩ := hg₂.band
  have hfin : ∫⁻ p, ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2) ∂measureH c ≠ ⊤ := by
    set K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) with hK_def
    have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    have hFc : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2 := by fun_prop
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hFc.continuousOn
    have hbound : ∫⁻ p, ENNReal.ofReal ((|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2) ∂measureH c
        ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal C) p ∂measureH c := by
      apply lintegral_mono_ae
      filter_upwards [ae_cell_measureH c] with p hp
      by_cases hpK : p ∈ K
      · rw [indicator_of_mem hpK]
        show ENNReal.ofReal _ ≤ ENNReal.ofReal C
        apply ENNReal.ofReal_le_ofReal
        have h := hC p hpK
        rwa [Real.norm_of_nonneg (by positivity)] at h
      · rw [indicator_of_notMem hpK]
        have hg0 : g₂ p = 0 := by
          by_contra hne
          obtain ⟨h1, h2⟩ := hb p hne
          exact hpK ⟨h1, ⟨hp.2.1.1.le, hp.2.1.2⟩, abs_le.1 h2⟩
        simp [hg0]
    have hmeasK : measureH c K < ⊤ := by
      rw [measureH, withDensity_apply _ hKm]
      calc ∫⁻ p in K, weightH p ∂cellMeasure c
          ≤ ∫⁻ _ in K, ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) ∂cellMeasure c := by
            refine setLIntegral_mono measurable_const fun p hp => ?_
            exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hp.1.1 (by norm_num))
        _ = ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) * cellMeasure c K := setLIntegral_const _ _
        _ < ⊤ := by
            refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
            calc cellMeasure c K ≤ volume K := Measure.restrict_apply_le _ _
              _ < ⊤ := hKc.measure_lt_top
    have hbk : ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal C) p ∂measureH c ≠ ⊤ := by
      rw [lintegral_indicator_const hKm]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmeasK.ne
    exact ne_top_of_le_ne_top hbk hbound
  -- real moments equal the `toReal` of their `lintegral`s
  have hnn₁ : 0 ≤ᵐ[measureH c] fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₁ p‖ ^ 2 :=
    ae_of_all _ fun p => by positivity
  have hnn₂ : 0 ≤ᵐ[measureH c] fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2 :=
    ae_of_all _ fun p => by positivity
  have hm₁ : AEStronglyMeasurable (fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₁ p‖ ^ 2)
      (measureH c) := by
    have : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₁ p‖ ^ 2 := by fun_prop
    exact this.aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable (fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2)
      (measureH c) := by
    have : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2 := by fun_prop
    exact this.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn₁ hm₁, integral_eq_lintegral_of_nonneg_ae hnn₂ hm₂]
  refine ENNReal.toReal_mono hfin ?_
  rw [mm_lint_eq c g₁ hcont₁ j, mm_lint_eq c g₂ hcont₂ j]
  -- the hypothesis on `q`-integrals over `(0, c]`
  have hQ : ∀ s η : ℝ, ∫ q in Ioc 0 c, ‖g₁ (s, q, η)‖ ^ 2 ≤ ∫ q in Ioc 0 c, ‖g₂ (s, q, η)‖ ^ 2 := by
    intro s η
    have h := hle s η
    rwa [intervalIntegral.integral_of_le hc.le, intervalIntegral.integral_of_le hc.le] at h
  refine lintegral_mono fun s => lintegral_mono fun η => ?_
  exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hQ s η)) zero_le

end UnforcedLeray.Short.PartIIa
