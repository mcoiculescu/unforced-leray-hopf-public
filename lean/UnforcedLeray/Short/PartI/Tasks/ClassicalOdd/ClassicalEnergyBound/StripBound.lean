import UnforcedLeray.Short.PartI.Sub.T02_3_10

/-!
# Part I, task `PartI:ClassicalOdd/ClassicalEnergyBound/StripBound`: the boundary strip estimate

Toolkit leaf `EbStripBound` (`Short/PartI/Sub/T02_3_10.lean`, line 116): there is `K₀ ≥ 0` with
`|∫_cell φ_R'(η) g| ≤ K₀ c B` for every `c > 0`, `R ≥ 1` and continuous `g` with `|g| ≤ B`, uniformly
in `R`.

Source of record: `the November 2 reference manuscript`, lines 276-282 (the energy
identities that use the transverse cutoffs). The strip estimate is the analytic consequence of
`EtaCutoffFacts` (`Short/PartI/Sub/T02_3.lean`, line 125).

## Strategy

Take `K₀ = 4 C₀`. By `EtaCutoffFacts`, `|φ_R'| ≤ (C₀/R) √φ_R ≤ C₀/R` everywhere, and `φ_R' = 0`
where `2R ≤ |η|`. So on the cell the integrand is dominated by `C₀/R · B` times the indicator of the
box `[-c/2, c/2) × [-2R, 2R]`, whose volume is `c · 4R`. The product `c · 4R · C₀/R · B` is
`4 C₀ c B`.
-/

open MeasureTheory

namespace UnforcedLeray.Short.PartI

/-- The box `[-c/2, c/2) × [-2R, 2R]` has real volume `c · 4R` (for `c, R ≥ 0`). -/
theorem ebStripBox_real (c R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R) :
    (volume : Measure (ℝ × ℝ)).real
        (Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)) = c * (4 * R) := by
  rw [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ c / 2 - -c / 2 by linarith),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 * R - -(2 * R) by linarith)]
  ring

/-- The box `[-c/2, c/2) × [-2R, 2R]` has finite volume. -/
theorem ebStripBox_ne_top (c R : ℝ) :
    (volume : Measure (ℝ × ℝ)) (Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- **Toolkit `EbStripBound`, from `EtaCutoffFacts`** (`K₀ = 4 C₀`). -/
theorem ebStripBound : EtaCutoffFacts → EbStripBound := by
  classical
  intro hF
  obtain ⟨C₀, hC₀, hfacts⟩ := hF
  unfold EbStripBound
  refine ⟨4 * C₀, by linarith, ?_⟩
  intro c R hc hR g B _hg hB
  have hR0 : 0 < R := by linarith
  have hRne : R ≠ 0 := hR0.ne'
  have hC0R : 0 ≤ C₀ / R := div_nonneg hC₀ hR0.le
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hK0 : 0 ≤ C₀ / R * B := mul_nonneg hC0R hB0
  have hSm : MeasurableSet (Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hcellm : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  -- the dominating function is integrable on the whole plane (finite-volume box)
  have hint_vol : Integrable
      ((Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)).indicator
        (fun _ : ℝ × ℝ => C₀ / R * B)) (volume : Measure (ℝ × ℝ)) :=
    (integrable_indicator_iff hSm).2 (integrableOn_const (ebStripBox_ne_top c R))
  -- pointwise bound on the cell
  have hpt : ∀ z ∈ UnforcedLeray.Cyl.cell c,
      ‖deriv (etaCutoff R) z.2 * g z‖ ≤
        (Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)).indicator
          (fun _ : ℝ × ℝ => C₀ / R * B) z := by
    intro z hz
    obtain ⟨_, hrange, _, hsupp, hderiv⟩ := hfacts R (by linarith)
    have hz1 : z.1 ∈ Set.Ico (-c / 2) (c / 2) :=
      (show z ∈ Set.Ico (-c / 2) (c / 2) ×ˢ (Set.univ : Set ℝ) from hz).1
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hin : z.2 ∈ Set.Icc (-(2 * R)) (2 * R)
    · have hmem : z ∈ Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R) := ⟨hz1, hin⟩
      rw [Set.indicator_of_mem hmem]
      have hs : Real.sqrt (etaCutoff R z.2) ≤ 1 := Real.sqrt_le_one.mpr (hrange z.2).2
      have h1 : |deriv (etaCutoff R) z.2| ≤ C₀ / R :=
        le_trans (hderiv z.2) (mul_le_of_le_one_right hC0R hs)
      exact mul_le_mul h1 (hB z) (abs_nonneg _) hC0R
    · have hout : z ∉ Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R) :=
        fun h => hin h.2
      rw [Set.indicator_apply, if_neg hout]
      have hlt : 2 * R ≤ |z.2| := by
        by_contra hlt
        have hlt' : |z.2| < 2 * R := not_le.mp hlt
        exact hin ⟨by linarith [neg_abs_le z.2], by linarith [le_abs_self z.2]⟩
      have h0 : |deriv (etaCutoff R) z.2| ≤ 0 := by
        have := hderiv z.2
        rwa [hsupp z.2 hlt, Real.sqrt_zero, mul_zero] at this
      have hd0 : deriv (etaCutoff R) z.2 = 0 := abs_nonpos_iff.mp h0
      simp [hd0]
  have hae : ∀ᵐ z ∂((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c)),
      ‖deriv (etaCutoff R) z.2 * g z‖ ≤
        (Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)).indicator
          (fun _ : ℝ × ℝ => C₀ / R * B) z :=
    (ae_restrict_mem hcellm).mono fun z hz => hpt z hz
  have hint : Integrable
      ((Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)).indicator
        (fun _ : ℝ × ℝ => C₀ / R * B))
      ((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c)) :=
    hint_vol.mono_measure Measure.restrict_le_self
  have hnonneg : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      (0 : ℝ) ≤ (Set.Ico (-c / 2) (c / 2) ×ˢ Set.Icc (-(2 * R)) (2 * R)).indicator
        (fun _ : ℝ × ℝ => C₀ / R * B) z :=
    ae_of_all _ fun z => Set.indicator_nonneg (fun _ _ => hK0) z
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le hint hae) ?_
  refine le_trans (integral_mono_measure Measure.restrict_le_self hnonneg hint_vol) ?_
  rw [integral_indicator_const _ hSm, smul_eq_mul, ebStripBox_real c R hc.le hR0.le]
  have hkey : c * (4 * R) * (C₀ / R * B) = 4 * C₀ * c * B := by
    field_simp
  exact hkey.le

end UnforcedLeray.Short.PartI
