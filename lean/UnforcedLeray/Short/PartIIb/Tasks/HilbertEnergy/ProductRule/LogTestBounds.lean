import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!
# Part II-b, task `PartII-b:T15/2/19`: basic bounds for logarithmic tests

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (the weak
product rule in the `H_2` measure, log chart `s = e^t`). The target is the Prop `LogTestBounds`
(`Sub/T15_2.lean`, leaf `PartII-b:T15/2/19`), proved unchanged.

Proof outline.
1. A `LogTest c Φ` is bounded: `Φ` is `c`-periodic in `q`, so each value equals a value with
   `q ∈ [-c/2, c/2]`, and `Φ` vanishes outside `|t| ≤ T, |η| ≤ L`; compactness bounds `Φ`.
2. `cpd 0 Φ` is continuous, `c`-periodic in `q` (translation invariance of `fderiv`), and vanishes
   outside the same region (it is zero on the open set where `Φ ≡ 0`), so step 1 applies to it.
3. Integrability: `logMeas c` is concentrated on the cell `q ∈ [-c/2, c/2)` (`ae`), so `f * g`
   agrees `logMeas c`-a.e. with its restriction to the compact box `W = [-T,T] × [-c/2,c/2] × [-L,L]`.
   On `W` the measure is finite, `f ∈ L²` gives `f ∈ L¹` there, and the bounded factor keeps
   integrability (`Integrable.bdd_mul`).
-/

set_option autoImplicit false

open scoped ENNReal ContDiff
open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

/-- A `q`-periodic, continuous function that vanishes outside `|t| ≤ T`, `|η| ≤ L` is bounded. -/
theorem logTestBounds_bounded {g : Coord → ℝ} {c T L : ℝ} (hc : 0 < c) (hg : Continuous g)
    (hper : ∀ x : Coord, g (qShift c x) = g x)
    (hzero : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → g x = 0) :
    ∃ C : ℝ, ∀ x : Coord, |g x| ≤ C := by
  have hK : IsCompact (Icc (-T) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : T < |x.1| ∨ L < |x.2.2|
  · rw [hzero x hx, abs_zero]
    exact le_max_right _ _
  · push_neg at hx
    have hper1 : Function.Periodic (fun q : ℝ => g (x.1, (q, x.2.2))) c :=
      fun q => hper (x.1, (q, x.2.2))
    obtain ⟨y, hy, hxy⟩ := hper1.exists_mem_Ico hc x.2.1 (-c / 2)
    have hxy' : g x = g (x.1, (y, x.2.2)) := hxy
    have hyc : y ∈ Icc (-c / 2) (c / 2) := by
      have h := Ico_subset_Icc_self hy
      rwa [show -c / 2 + c = c / 2 by ring] at h
    have hmem : (x.1, (y, x.2.2)) ∈ Icc (-T) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
      ⟨abs_le.mp hx.1, hyc, abs_le.mp hx.2⟩
    have hb := hC _ hmem
    rw [hxy', ← Real.norm_eq_abs]
    exact hb.trans (le_max_left _ _)

/-- The derivative `cpd 0 Φ = ∂_t Φ` of a smooth function is continuous. -/
theorem logTestBounds_cpd_continuous {Φ : Coord → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (cpd 0 Φ) := by
  have h1 : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by simp)
  show Continuous fun x => fderiv ℝ Φ x (cdir 0)
  exact h1.clm_apply continuous_const

/-- `cpd 0 Φ` is again `c`-periodic in `q` when `Φ` is. -/
theorem logTestBounds_cpd_periodic {c : ℝ} {Φ : Coord → ℝ}
    (hper : ∀ x : Coord, Φ (qShift c x) = Φ x) :
    ∀ x : Coord, cpd 0 Φ (qShift c x) = cpd 0 Φ x := by
  have hsh : ∀ y : Coord, qShift c y = y + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) := fun y => by
    show (y.1, (y.2.1 + c, y.2.2)) = (y.1 + 0, (y.2.1 + c, y.2.2 + 0))
    simp
  have hinv : (fun y : Coord => Φ (y + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) = Φ := by
    funext y
    rw [← hsh y]
    exact hper y
  have key : ∀ y : Coord, fderiv ℝ Φ y = fderiv ℝ Φ (y + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
    fun y => by
      have h2 : fderiv ℝ (fun z : Coord => Φ (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))))  y =
          fderiv ℝ Φ (y + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
        fderiv_comp_add_right _
      have h3 : fderiv ℝ (fun z : Coord => Φ (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) y =
          fderiv ℝ Φ y := by
        rw [hinv]
      exact h3.symm.trans h2
  intro x
  show fderiv ℝ Φ (qShift c x) (cdir 0) = fderiv ℝ Φ x (cdir 0)
  rw [hsh x, key x]

/-- If `Φ` vanishes on the open set `|t| > T` or `|η| > L`, so does `cpd 0 Φ`. -/
theorem logTestBounds_cpd_zero {Φ : Coord → ℝ} {T L : ℝ}
    (hTL : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → Φ x = 0) :
    ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → cpd 0 Φ x = 0 := by
  intro x hx
  have hopen : IsOpen {y : Coord | T < |y.1| ∨ L < |y.2.2|} := by
    have h1 : IsOpen {y : Coord | T < |y.1|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
    have h2 : IsOpen {y : Coord | L < |y.2.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))
    exact h1.union h2
  have hev : Φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hTL y hy
  show fderiv ℝ Φ x (cdir 0) = 0
  rw [hev.fderiv_eq]
  simp

/-- Integrability of `f * g` against `logMeas c` for `f ∈ L²` and a bounded continuous `g` that
vanishes outside `|t| ≤ T`, `|η| ≤ L`. The measure lives on the cell `q ∈ [-c/2, c/2)`. -/
theorem logTestBounds_integrable {c T L C : ℝ} (hc : 0 < c) {f : Coord → ℂ}
    (hf : MemLp f 2 (logMeas c)) {g : Coord → ℝ} (hg : Continuous g)
    (hC : ∀ x : Coord, |g x| ≤ C) (hzero : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → g x = 0) :
    Integrable (fun x => f x * ((g x : ℝ) : ℂ)) (logMeas c) := by
  -- the cell measure `avgμ c` is an `SFinite` measure (needed for `Measure.prod_prod`)
  have hSF : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ Cyl.cellμ
    infer_instance
  obtain ⟨W, hW⟩ : ∃ W : Set Coord, W = Icc (-T) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
    ⟨_, rfl⟩
  have hWm : MeasurableSet W := by
    rw [hW]
    exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).isClosed.measurableSet
  have hmemW : ∀ x : Coord, |x.1| ≤ T → x.2.1 ∈ Icc (-c / 2) (c / 2) → |x.2.2| ≤ L → x ∈ W :=
    fun x h1 h2 h3 => by
      rw [hW]
      exact ⟨abs_le.mp h1, h2, abs_le.mp h3⟩
  -- finiteness of `logMeas c` on the box
  have hfin : logMeas c W < ⊤ := by
    have hB : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L : Set (ℝ × ℝ)) < ⊤ :=
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    rw [hW, logMeas, Measure.prod_prod]
    refine ENNReal.mul_lt_top measure_Icc_lt_top ?_
    rw [Cyl.avgμ, Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [Cyl.cellμ]
    exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) hB
  -- `logMeas c` is concentrated on the cell `q ∈ [-c/2, c/2)`
  have hae : ∀ᵐ x ∂(logMeas c), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
    rw [ae_iff]
    have hcellm : MeasurableSet (Cyl.cell c) := measurableSet_Ico.prod MeasurableSet.univ
    have h0 : Cyl.avgμ c (Cyl.cell c)ᶜ = 0 := by
      rw [Cyl.avgμ, Measure.smul_apply, Cyl.cellμ, Measure.restrict_apply' hcellm,
        compl_inter_self, measure_empty, smul_zero]
    refine measure_mono_null (t := (Set.univ : Set ℝ) ×ˢ (Cyl.cell c)ᶜ) ?_ ?_
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      exact ⟨Set.mem_univ _, fun h => hx (Set.mem_prod.1 (show x.2 ∈ Ico (-c / 2) (c / 2) ×ˢ univ
        from h)).1⟩
    · rw [logMeas, Measure.prod_prod, h0, mul_zero]
  haveI : IsFiniteMeasure ((logMeas c).restrict W) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfin⟩
  have hfI : Integrable f ((logMeas c).restrict W) :=
    (hf.restrict W).integrable one_le_two
  have hgm : AEStronglyMeasurable (fun x : Coord => ((g x : ℝ) : ℂ)) ((logMeas c).restrict W) :=
    (Complex.continuous_ofReal.comp hg).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂((logMeas c).restrict W), ‖((g x : ℝ) : ℂ)‖ ≤ C :=
    Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC x
  have hint : Integrable (fun x => f x * ((g x : ℝ) : ℂ)) ((logMeas c).restrict W) :=
    (hfI.bdd_mul hgm hbd).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hind : Integrable (W.indicator (fun x => f x * ((g x : ℝ) : ℂ))) (logMeas c) :=
    (integrable_indicator_iff hWm).2 hint
  refine hind.congr ?_
  filter_upwards [hae] with x hx
  by_cases hxW : x ∈ W
  · rw [Set.indicator_of_mem hxW]
  · rw [Set.indicator_of_notMem hxW]
    have hz : g x = 0 := by
      apply hzero x
      by_contra hcon
      push_neg at hcon
      exact hxW (hmemW x hcon.1 (Ico_subset_Icc_self hx) hcon.2)
    simp [hz]

/-- **Leaf `PartII-b:T15/2/19`** (basic bounds for logarithmic tests). -/
theorem logTestBounds : UnforcedLeray.Short.IIb.LogTestBounds := by
  intro c Φ hc hΦ
  obtain ⟨T, L, hTL⟩ := hΦ.compact
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  obtain ⟨C₀, hC₀⟩ := logTestBounds_bounded hc hΦc hΦ.periodic hTL
  have hD : Continuous (cpd 0 Φ) := logTestBounds_cpd_continuous hΦ.smooth
  obtain ⟨C₁, hC₁⟩ :=
    logTestBounds_bounded hc hD (logTestBounds_cpd_periodic hΦ.periodic)
      (logTestBounds_cpd_zero hTL)
  refine ⟨⟨C₀, hC₀⟩, ⟨C₁, hC₁⟩, fun f hf => ⟨?_, ?_⟩⟩
  · exact logTestBounds_integrable hc hf hΦc hC₀ hTL
  · exact logTestBounds_integrable hc hf hD hC₁ (logTestBounds_cpd_zero hTL)

end UnforcedLeray.Short.IIb
