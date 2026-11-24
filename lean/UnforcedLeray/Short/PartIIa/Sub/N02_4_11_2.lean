import UnforcedLeray.Short.PartIIa.Sub.N02_4_11

/-!
# Part II-a, decomposition of `PartII-a:N02/4/11/2` (`nzSliceToL2`)

Source of record: `the November 2 reference manuscript`, lines 1744-1749
(slice convergence of the `q`-Fourier truncations implies `L²(measureH c)` convergence).

`nzSliceToL2_of` derives `NzSliceToL2` from five elementary measure-theoretic facts: continuity of
the truncations, the Fubini formula for `measureH c` in the `(s, η)`-coordinates, finiteness of a
band box for the `(s, η)`-measure, the conversion of `q`-slice lintegrals to interval integrals,
and a global bound on a smooth band test of period `c > 0`. The dominated convergence argument is
carried out here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The `(s, η)`-measure `s^{-3/2} ds dη` on `(0, ∞) × ℝ` obtained from `measureH c` after
integrating out `q` over `(0, c]`. -/
def NzsMeasureSE : Measure (ℝ × ℝ) :=
  ((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun s : ℝ => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))))).prod volume

/-- **Sub1.** The Fourier truncations of a smooth band test are continuous (parametric integral
over the compact interval `[0, c]` of a continuous integrand, then a finite sum). Source 1744-1749. -/
def NzsTruncCont : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f →
    ∀ N : ℕ, Continuous (nzTrunc c N f)

/-- **Sub2.** Fubini/Tonelli for `measureH c = (s^{-3/2} ds dq dη)|_{cell}`: `Profile = ℝ × ℝ × ℝ`,
`q` is the middle coordinate and the cell is `Ioi 0 ×ˢ Ioc 0 c ×ˢ univ` (`lintegral_withDensity_eq_lintegral_mul`,
`Measure.restrict_prod_eq_prod_univ`/`lintegral_prod`, `lintegral_prod_symm`). Source 1744-1749. -/
def NzsFubini : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Profile → ℝ≥0∞, Measurable F →
    ∫⁻ p, F p ∂(measureH c) =
      ∫⁻ x : ℝ × ℝ, (∫⁻ q in Ioc (0 : ℝ) c, F (x.1, q, x.2)) ∂NzsMeasureSE

/-- **Sub3.** A band box `Icc s0 s1 ×ˢ Icc (-L) L` with `0 < s0` has finite `NzsMeasureSE`-measure
(`Measure.prod_prod`, `withDensity_apply`, the weight `s^{-3/2}` is bounded by `s0^{-3/2}` on `Icc s0 s1`). -/
def NzsBandFinite : Prop :=
  ∀ s0 s1 L : ℝ, 0 < s0 → NzsMeasureSE (Icc s0 s1 ×ˢ Icc (-L) L) ≠ ⊤

/-- **Sub4.** A `q`-slice lintegral of `‖g‖²` of a continuous profile equals the `ofReal` of the
interval integral (`intervalIntegral.integral_of_le`, `ofReal_integral_eq_lintegral_ofReal`; the
integrand is continuous in `q`, hence interval integrable on the compact `[0, c]`). -/
def NzsSliceLintegral : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ g : Profile → MeridC, Continuous g → ∀ s η : ℝ,
    ∫⁻ q in Ioc (0 : ℝ) c, ‖g (s, q, η)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∫ q in (0 : ℝ)..c, ‖g (s, q, η)‖ ^ 2)

/-- **Sub5.** A smooth band test of period `c > 0` is bounded: by `c`-periodicity in `q`
(`Function.Periodic.exists_mem_Ico₀`) its values are those on the compact box
`Icc s0 s1 ×ˢ Icc 0 c ×ˢ Icc (-L) L`, where it is continuous
(`IsCompact.exists_bound_of_continuousOn`), and it vanishes off the band. The period `c > 0` is
the standing assumption of the section (`P = 2εc ≤ 1` and the measure `ds dq/c dη`, source
lines 1637-1643); at `c = 0` periodicity is vacuous and a band test can be unbounded in `q`.
Source 1744-1749. -/
def NzsBound : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f →
    ∃ M : ℝ, ∀ p : Profile, ‖f p‖ ≤ M

theorem nzSliceToL2_of (hCont : NzsTruncCont) (hFub : NzsFubini) (hBand : NzsBandFinite)
    (hSl : NzsSliceLintegral) (hBd : NzsBound) : NzSliceToL2 := by
  intro hSC c hc f hf hq
  have hg : ∀ N : ℕ, Continuous (fun p => nzTrunc c N f p - f p) := fun N =>
    (hCont c hc f hf N).sub hf.smooth.continuous
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  obtain ⟨M, hM⟩ := hBd c hc f hf
  let Fn : ℕ → Profile → ℝ≥0∞ := fun N p => ‖nzTrunc c N f p - f p‖ₑ ^ (2 : ℝ)
  have hFm : ∀ N, Measurable (Fn N) := fun N => (hg N).measurable.enorm.pow_const _
  let K : ℕ → ℝ × ℝ → ℝ≥0∞ := fun N x => ∫⁻ q in Ioc (0 : ℝ) c, Fn N (x.1, q, x.2)
  have key : ∀ N, ∫⁻ p, Fn N p ∂(measureH c) = ∫⁻ x, K N x ∂NzsMeasureSE :=
    fun N => hFub c hc _ (hFm N)
  have hKeq : ∀ N x, K N x = ENNReal.ofReal
      (∫ q in (0 : ℝ)..c, ‖nzTrunc c N f (x.1, q, x.2) - f (x.1, q, x.2)‖ ^ 2) :=
    fun N x => hSl c hc _ (hg N) x.1 x.2
  have hKm : ∀ N, Measurable (K N) := by
    intro N
    have h1 : Measurable (fun z : (ℝ × ℝ) × ℝ => Fn N (z.1.1, z.2, z.1.2)) :=
      (hFm N).comp (by fun_prop)
    exact h1.lintegral_prod_right'
  have hlim : ∀ x, Tendsto (fun N => K N x) atTop (𝓝 0) := by
    intro x
    have h := ENNReal.tendsto_ofReal (hSC c hc f hf hq x.1 x.2).1
    simp only [ENNReal.ofReal_zero] at h
    exact h.congr (fun N => (hKeq N x).symm)
  let C : ℝ≥0∞ := ENNReal.ofReal (4 * (M ^ 2 * c))
  let B : Set (ℝ × ℝ) := Icc s0 s1 ×ˢ Icc (-L) L
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hbound : ∀ N x, K N x ≤ B.indicator (fun _ => C) x := by
    intro N x
    rw [hKeq]
    have h2 := (hSC c hc f hf hq x.1 x.2).2 N
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      refine h2.trans ?_
      have hle : ∫ q in (0 : ℝ)..c, ‖f (x.1, q, x.2)‖ ^ 2 ≤ M ^ 2 * c := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := c)
          (C := M ^ 2) (f := fun q => ‖f (x.1, q, x.2)‖ ^ 2) (by
            intro q _
            have h0 := hM (x.1, q, x.2)
            rw [norm_pow, norm_norm]
            exact pow_le_pow_left₀ (norm_nonneg _) h0 2)
        calc _ ≤ ‖∫ q in (0 : ℝ)..c, ‖f (x.1, q, x.2)‖ ^ 2‖ := Real.le_norm_self _
          _ ≤ M ^ 2 * |c - 0| := this
          _ = M ^ 2 * c := by rw [sub_zero, abs_of_pos hc]
      linarith
    · rw [indicator_of_notMem hx]
      have hz : ∀ q, f (x.1, q, x.2) = 0 := by
        intro q
        by_contra hne
        obtain ⟨h1, h3⟩ := hb _ hne
        exact hx ⟨h1, abs_le.1 h3⟩
      have h0 : ∫ q in (0 : ℝ)..c, ‖f (x.1, q, x.2)‖ ^ 2 = 0 := by
        simp [hz]
      rw [h0] at h2
      exact ENNReal.ofReal_of_nonpos (by linarith) |>.le
  have hfin : ∫⁻ x, B.indicator (fun _ => C) x ∂NzsMeasureSE ≠ ⊤ := by
    rw [lintegral_indicator_const hBm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hBand s0 s1 L hs0)
  have hT := tendsto_lintegral_of_dominated_convergence (μ := NzsMeasureSE)
    (B.indicator (fun _ => C)) hKm
    (fun N => ae_of_all _ (hbound N)) hfin (ae_of_all _ hlim)
  simp only [lintegral_zero] at hT
  have hI : Tendsto (fun N => ∫⁻ p, Fn N p ∂(measureH c)) atTop (𝓝 0) := by
    refine hT.congr (fun N => ?_)
    exact (key N).symm
  have h3 := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hI
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  refine h3.congr (fun N => ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp [Fn, Function.comp]

end UnforcedLeray.Short.PartIIa
