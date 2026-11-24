import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The `η`-integral of `κ₀·(essSup_q W|a|)²·(cell integral)` (helper for `FarOutChartQ`)

Source `the November 2 reference manuscript` 2713-2721 (`‖Wv(s)‖_{L²_ηL^∞_q}`),
2666-2689 (the cell `|q| < c/2`, `dς = ds dq/c dη`).

In `FarOutChartQ` (`Kernel/ThinRecv.lean`) the coefficient `a` is arbitrary, so
`M(η) = essSup_q W|a|(s,q,η)` need not be measurable in `η`, and `∫_η` is the lower Lebesgue
integral.  The bound `∫_η∫_q H ≤ κ₀K∫_η M²` from `H ≤ κ₀M(η)²|v|²` and `∫_q|v|² ≤ K` then cannot
pull the constant `K = 2s⁻¹Φ(s)²` out of `∫_η κ₀M²K` when `K = ⊤` (`lintegral_mul_const'` needs
`K ≠ ⊤`; for a non-measurable `M` with lower integral `0` and `M > 0` everywhere the pull-out is
false).  `etaPull` proves the bound for every `K ≤ ⊤` and finite `κ₀` by dividing the measurable
`∫_q H` by the measurable `κ₀∫_q|v|²` (a measurable minorant of `M²`) after truncating `|v|² ≤ N`
(monotone convergence).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.ChartQEtaPull

/-- The `η`-level pull-out with a finite measurable cell integral `J`. -/
private theorem pull_of_finite {L J M : ℝ → ℝ≥0∞} {κ₀ K : ℝ≥0∞} (hk : κ₀ ≠ ⊤)
    (hL : Measurable L) (hJ : Measurable J) (hJt : ∀ η, J η ≠ ⊤) (hJK : ∀ᵐ η, J η ≤ K)
    (hLM : ∀ᵐ η, L η ≤ κ₀ * M η * J η) : ∫⁻ η, L η ≤ κ₀ * K * ∫⁻ η, M η := by
  set ψ : ℝ → ℝ≥0∞ := fun η => L η / (κ₀ * J η) with hψdef
  have hψ : Measurable ψ := hL.div (measurable_const.mul hJ)
  have hre : ∀ η, κ₀ * M η * J η = M η * (κ₀ * J η) := fun η => by ring
  have h1 : ∀ᵐ η, ψ η ≤ M η := by
    filter_upwards [hLM] with η hη
    exact ENNReal.div_le_of_le_mul (hη.trans_eq (hre η))
  have h2 : ∀ᵐ η, L η ≤ ψ η * (κ₀ * K) := by
    filter_upwards [hLM, hJK] with η hη hjk
    rcases eq_or_ne (κ₀ * J η) 0 with h0 | h0
    · have hL0 : L η = 0 := le_antisymm ((hη.trans_eq (hre η)).trans_eq (by rw [h0, mul_zero]))
        (zero_le)
      rw [hL0]; exact zero_le
    · have hne : κ₀ * J η ≠ ⊤ := ENNReal.mul_ne_top hk (hJt η)
      calc L η = ψ η * (κ₀ * J η) := (ENNReal.div_mul_cancel h0 hne).symm
        _ ≤ ψ η * (κ₀ * K) := by gcongr
  calc ∫⁻ η, L η ≤ ∫⁻ η, ψ η * (κ₀ * K) := lintegral_mono_ae h2
    _ = (∫⁻ η, ψ η) * (κ₀ * K) := lintegral_mul_const _ hψ
    _ ≤ (∫⁻ η, M η) * (κ₀ * K) := mul_le_mul_left (lintegral_mono_ae h1) _
    _ = κ₀ * K * ∫⁻ η, M η := mul_comm _ _

/-- **The `η`-integral of the cell bound** (source 2713-2721, 2666-2689): for a finite measure `ν`
in `q` (the cell `Ico (-(c/2)) (c/2)`), measurable `h, w ≥ 0` on `(q, η)` with `w < ⊤`,
an arbitrary (possibly non-measurable) `M : ℝ → ℝ≥0∞`, `κ₀ ≠ ⊤` and any `K ≤ ⊤`:
if for a.e. `η`, `h(q,η) ≤ κ₀M(η)w(q,η)` for `ν`-a.e. `q` and `∫_q w(q,η)dν ≤ K`, then
`∫_η∫_q h dν ≤ κ₀K∫_η M`.  (Use with `h = c⁻¹·H(s,·)`, `w = c⁻¹·‖v(s,·)‖ₑ²` or `ν = c⁻¹·vol`,
`M = (essSup_q W‖a‖ₑ)²`, `K = 2s⁻¹Φ(s)²`.) -/
theorem etaPull {ν : Measure ℝ} [IsFiniteMeasure ν] {h w : ℝ × ℝ → ℝ≥0∞} {M : ℝ → ℝ≥0∞}
    {κ₀ K : ℝ≥0∞} (hk : κ₀ ≠ ⊤) (hh : Measurable h) (hw : Measurable w) (hwt : ∀ x, w x ≠ ⊤)
    (hle : ∀ᵐ η, ∀ᵐ q ∂ν, h (q, η) ≤ κ₀ * M η * w (q, η))
    (hK : ∀ᵐ η, ∫⁻ q, w (q, η) ∂ν ≤ K) :
    ∫⁻ η, ∫⁻ q, h (q, η) ∂ν ≤ κ₀ * K * ∫⁻ η, M η := by
  set T : ℕ → Set (ℝ × ℝ) := fun N => {x | w x ≤ N} with hTdef
  have hT : ∀ N, MeasurableSet (T N) := fun N => measurableSet_le hw measurable_const
  set hN : ℕ → ℝ × ℝ → ℝ≥0∞ := fun N => (T N).indicator h with hNdef
  set wN : ℕ → ℝ × ℝ → ℝ≥0∞ := fun N => (T N).indicator w with wNdef
  have hNm : ∀ N, Measurable (hN N) := fun N => hh.indicator (hT N)
  have wNm : ∀ N, Measurable (wN N) := fun N => hw.indicator (hT N)
  have hmono : Monotone hN := by
    intro N N' hNN' x
    by_cases hx : x ∈ T N
    · have hx' : x ∈ T N' := (show w x ≤ N from hx).trans (by exact_mod_cast hNN')
      simp only [hN, indicator_of_mem hx, indicator_of_mem hx', le_refl]
    · simp only [hN, indicator_of_notMem hx]; exact zero_le
  have hsup : ∀ x, ⨆ N, hN N x = h x := by
    intro x
    obtain ⟨N, hN'⟩ := ENNReal.exists_nat_gt (hwt x)
    refine le_antisymm (iSup_le fun N => indicator_le_self _ _ x) (le_iSup_of_le N ?_)
    have hx : x ∈ T N := hN'.le
    simp only [hN, indicator_of_mem hx, le_refl]
  have hstep : ∀ N : ℕ, ∫⁻ η, ∫⁻ q, hN N (q, η) ∂ν ≤ κ₀ * K * ∫⁻ η, M η := by
    intro N
    refine pull_of_finite (J := fun η => ∫⁻ q, wN N (q, η) ∂ν) hk (hNm N).lintegral_prod_left'
      (wNm N).lintegral_prod_left' (fun η => ?_) ?_ ?_
    · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N)
        (measure_ne_top ν univ)) ?_
      calc ∫⁻ q, wN N (q, η) ∂ν ≤ ∫⁻ _q, (N : ℝ≥0∞) ∂ν := lintegral_mono fun q => by
            by_cases hq : (q, η) ∈ T N
            · simp only [wN, indicator_of_mem hq]; exact hq
            · simp only [wN, indicator_of_notMem hq]; exact zero_le
        _ = N * ν univ := lintegral_const _
    · filter_upwards [hK] with η hη
      exact (lintegral_mono fun q => indicator_le_self _ _ _).trans hη
    · filter_upwards [hle] with η hη
      calc ∫⁻ q, hN N (q, η) ∂ν ≤ ∫⁻ q, κ₀ * M η * wN N (q, η) ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [hη] with q hq
            by_cases hm : (q, η) ∈ T N
            · simp only [hN, wN, indicator_of_mem hm]; exact hq
            · simp only [hN, wN, indicator_of_notMem hm, mul_zero, le_refl]
        _ = κ₀ * M η * ∫⁻ q, wN N (q, η) ∂ν :=
            lintegral_const_mul _ ((wNm N).comp measurable_prodMk_right)
  calc ∫⁻ η, ∫⁻ q, h (q, η) ∂ν = ∫⁻ η, ⨆ N, ∫⁻ q, hN N (q, η) ∂ν := by
        refine lintegral_congr fun η => ?_
        have hI := lintegral_iSup (μ := ν) (f := fun N q => hN N (q, η))
          (fun N => (hNm N).comp measurable_prodMk_right) (fun N N' hNN' q => hmono hNN' (q, η))
        rw [← hI]
        simp only [hsup]
    _ = ⨆ N, ∫⁻ η, ∫⁻ q, hN N (q, η) ∂ν :=
        lintegral_iSup (fun N => (hNm N).lintegral_prod_left')
          (fun N N' hNN' η => lintegral_mono fun q => hmono hNN' (q, η))
    _ ≤ _ := iSup_le hstep

/-- Product-a.e. on `(q, η)` gives a.e. `η`, then a.e. `q` (any predicate; measurable null
superset and `Measure.prod_apply_symm`). -/
theorem ae_slices {ν : Measure ℝ} [SFinite ν] {P : ℝ × ℝ → Prop}
    (hP : ∀ᵐ x ∂(ν.prod volume), P x) : ∀ᵐ η, ∀ᵐ q ∂ν, P (q, η) := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hP)
  rw [Measure.prod_apply_symm hNm] at hN0
  have h0 := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hNm)).1 hN0
  filter_upwards [h0] with η hη
  exact ae_iff.2 (measure_mono_null (fun q hq => hsub hq) hη)

/-- `etaPull` with the pointwise bound a.e. for the product measure `ν ⊗ dη` on `(q, η)`. -/
theorem etaPull' {ν : Measure ℝ} [IsFiniteMeasure ν] {h w : ℝ × ℝ → ℝ≥0∞} {M : ℝ → ℝ≥0∞}
    {κ₀ K : ℝ≥0∞} (hk : κ₀ ≠ ⊤) (hh : Measurable h) (hw : Measurable w) (hwt : ∀ x, w x ≠ ⊤)
    (hle : ∀ᵐ x ∂(ν.prod volume), h x ≤ κ₀ * M x.2 * w x)
    (hK : ∀ᵐ η, ∫⁻ q, w (q, η) ∂ν ≤ K) :
    ∫⁻ η, ∫⁻ q, h (q, η) ∂ν ≤ κ₀ * K * ∫⁻ η, M η :=
  etaPull hk hh hw hwt (ae_slices (P := fun x => h x ≤ κ₀ * M x.2 * w x) hle) hK

end UnforcedLeray.Short.PartIIIb.Concrete.ChartQEtaPull
