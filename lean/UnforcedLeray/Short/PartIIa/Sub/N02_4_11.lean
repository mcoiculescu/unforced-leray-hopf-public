import UnforcedLeray.Short.PartIIa.Sub.N02_4_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!
# Part II-a, `PartII-a:N02/4/11` decomposition: `NzTruncConverge` from slice convergence and Fubini/DCT

Target: `nzTruncConverge : NzTruncConverge` (`Sub/N02_4_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

This file proves the reduction `nztc_of_l2 : NzTruncL2 → NzTruncConverge`. The remaining analytic
input `NzTruncL2` (the `L²(measureH c)`-error of the Fourier truncations tends to zero) is stated as


* the truncations are `IsMeridTest` (hence `L²(measureH c)`) by `nzTruncTest_of` applied to the
  proved leaf `intervalParamSmooth_proof`;
* `F` is identified with `f` in `L²`, and the `L²` convergence of the classes follows from the
  `eLpNorm` convergence `NzTruncL2` (`Lp.tendsto_Lp_iff_tendsto_eLpNorm''`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Analytic input NzTruncL2: the Fourier truncations converge in `L²(measureH c)`.** For a smooth
band test `f` with zero `q`-mean, `‖f_N - f‖_{L²(measureH c)} → 0` as `N → ∞`. Proof plan (not yet
formalized): (a) for each `(s, η)`, the `q`-slice error
`∫_0^c ‖f_N - f‖² dq` tends to `0` (Parseval for the `q`-Fourier series of the zero-mean smooth
periodic slice, `hasSum_sq_fourierCoeffOn`, `fourierCoeff_fourier`), and it is bounded by
`4 ∫_0^c ‖f‖² dq` (Bessel, the tail of Parseval); (b) integrate against `measureH c` by Fubini
(`MeasureTheory.lintegral_prod`, the `q`-coordinate is the middle coordinate of `Profile`) and
dominated convergence (`tendsto_lintegral_of_dominated_convergence`), the dominating function being
`4 ∫_0^c ‖f‖² dq`, which is bounded and supported in the band. -/
def NzTruncL2 : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → QMeanZero c f →
    Tendsto (fun N : ℕ => eLpNorm (nzTrunc c N f - f) 2 (measureH c)) atTop (𝓝 0)

/-- A smooth band test is in `L²(measureH c)`: it is continuous and vanishes off the compact band
`Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)`, which has finite `measureH c`-measure. -/
theorem nztc_memLp {c : ℝ} {g : Profile → MeridC} (hg : IsMeridTest c g) :
    MemLp g 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hg.band
  refine memLp_of_continuous_of_ae_vanish hg.smooth.continuous
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (measureH_band_ne_top c hs0 s1 L) ?_ 2
  filter_upwards [ae_cell_measureH c] with p hp
  intro hpA
  by_contra hne
  obtain ⟨h1, h2⟩ := hb p hne
  exact hpA ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩

/-- **Reduction: `L²` truncation convergence gives `NzTruncConverge`.** The classes `F_N` are the
`L²`-classes of the truncations `nzTrunc c N f`, which are `L²(measureH c)` by `nzTruncTest_of`. -/
theorem nztc_of_l2 (hL : NzTruncL2) : NzTruncConverge := by
  intro c hc f hf hT F hF
  have hmem : ∀ N : ℕ, MemLp (nzTrunc c N f) 2 (measureH c) := fun N =>
    nztc_memLp ((nzTruncTest_of intervalParamSmooth_proof) c hc f hf hT N).1
  have hfL : MemLp f 2 (measureH c) := nztc_memLp hf
  have hFeq : F = hfL.toLp f :=
    Lp.ext (by
      filter_upwards [hF, hfL.coeFn_toLp] with p h1 h2
      rw [h1, h2])
  refine ⟨fun N => (hmem N).toLp (nzTrunc c N f), fun N => (hmem N).coeFn_toLp, ?_⟩
  rw [hFeq]
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N => nzTrunc c N f) hmem f hfL).mpr (hL c hc f hf hT)

/-- **Leaf A.** Per-slice convergence: for each `(s, η)` the `q`-slice `L²(0,c)`-error of the
truncations tends to `0` and is bounded by `4 ∫_0^c ‖f‖² dq` (Parseval/Bessel for the zero-mean
slice; source lines 1744-1749). -/
def NzSliceConv : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → QMeanZero c f →
    ∀ s η : ℝ,
      Tendsto (fun N : ℕ => ∫ q in (0:ℝ)..c, ‖nzTrunc c N f (s, q, η) - f (s, q, η)‖ ^ 2)
        atTop (𝓝 0) ∧
      ∀ N : ℕ, ∫ q in (0:ℝ)..c, ‖nzTrunc c N f (s, q, η) - f (s, q, η)‖ ^ 2
        ≤ 4 * ∫ q in (0:ℝ)..c, ‖f (s, q, η)‖ ^ 2

/-- **Leaf B.** Fubini over `measureH c` plus dominated convergence: slice convergence gives the
`L²(measureH c)` convergence. -/
def NzSliceToL2 : Prop := NzSliceConv → NzTruncL2

/-- Decomposition: `nzTruncConverge` follows from the two leaves. -/
theorem nzTruncConverge_of (hA : NzSliceConv) (hB : NzSliceToL2) : NzTruncConverge :=
  nztc_of_l2 (hB hA)

end UnforcedLeray.Short.PartIIa
