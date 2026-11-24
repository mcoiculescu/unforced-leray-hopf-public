import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull

/-!
# The `L²` identity for the source tensor on the chart (source 2666-2668, 2675-2683)

`chartL2Source_of`: for fixed `τ`, the axisymmetric polar reduction (`PolarReduction`, `lo = 0`,
the axis is null) gives `∫_{ℝ³} gAx² = 2π ∫_{ρ>0}∫_t ρ gAx(τ, ρ, t)²`; `ChartChange` (`lo = 0`)
turns the `τ`-integral into `R c ∫ gAx(chartTau, chartY)² d(ageμ c (-5/2))`. On the cell
`q ∈ [-c/2, c/2)` one has `chartOf (chartY x) (chartTau x) = x`, so `gAx(chartTau, chartY) =
s · |nsSym f|`, and the age shift `s^{-2}` (`AgeShift` with `b = -2`) converts `s^{-5/2}` into
`s^{-1/2}` times `s²` cancelling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

private lemma cs_ptOf_meas : Measurable (fun u : ℝ × ℝ => ptOf u.1 u.2) := by
  apply Continuous.measurable
  unfold ptOf
  have h3 : Continuous (fun u : ℝ × ℝ => (![u.1, 0, u.2] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 _).comp h3

private lemma cs_sqrt_meas : Measurable (fun s : ℝ => Real.sqrt s) :=
  Real.continuous_sqrt.measurable

/-- The chart point of `chartY` lies on the cell: `chartOf` inverts `(chartY, chartTau)`. -/
private lemma cs_chartOf_chartY (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (x : Chart) (hs : 0 < x.1)
    (hq : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    chartOf R c (chartY R x) (chartTau R x) = x := by
  have hsq : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hs
  have h0 : (chartY R x) 0 = R / Real.sqrt x.1 := by simp [chartY]
  have h1 : (chartY R x) 1 = 0 := by simp [chartY]
  have h2 : (chartY R x) 2 = x.2.2 / Real.sqrt x.1 := by simp [chartY]
  have hr : hRad (chartY R x) = R / Real.sqrt x.1 := by
    unfold hRad
    rw [h0, h1, show (R / Real.sqrt x.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt x.1) ^ 2 by ring]
    exact Real.sqrt_sq (div_nonneg hR.le hsq.le)
  have hlog : Real.log (hRad (chartY R x) / R) = -(Real.log x.1) / 2 := by
    rw [hr, show R / Real.sqrt x.1 / R = (Real.sqrt x.1)⁻¹ by field_simp, Real.log_inv,
      Real.log_sqrt hs.le]
    ring
  have hin : R * Real.log (hRad (chartY R x) / R) + R * chartTau R x / 2 = x.2.1 := by
    rw [hlog]
    unfold chartTau
    field_simp
    ring
  have hfl : ⌊x.2.1 / c + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    obtain ⟨hq1, hq2⟩ := hq
    constructor
    · have : -(1 / 2 : ℝ) ≤ x.2.1 / c := by
        rw [le_div_iff₀ hc]
        linarith
      linarith
    · have : x.2.1 / c < 1 / 2 := by
        rw [div_lt_iff₀ hc]
        linarith
      linarith
  unfold chartOf
  rw [hin, hfl, hr, h2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    field_simp
    rw [Real.sq_sqrt hs.le]
  · simp
  · simp only
    field_simp

/-- The `L²(ageμ c (-1/2))` identity for the source tensor on the chart (source 2683). -/
theorem chartL2Source_of (hS : AgeShift) (hP : PolarReduction) (hC : ChartChange)
    (hG : GAxFacts) : ChartL2Source := by
  intro R c hR hc f hf
  obtain ⟨hax, hper, hgm⟩ := hG R c f hR hc hf
  have hTm : Measurable (fun T : Ten3 => UnforcedLeray.Short.IIIa.tensorNorm (nsSym T)) := by
    apply Continuous.measurable
    unfold UnforcedLeray.Short.IIIa.tensorNorm nsSym symRZ
    fun_prop
  have hGm : Measurable (fun x : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ)) :=
    (ENNReal.measurable_ofReal.comp (hTm.comp hf)).pow_const _
  -- Step 1: the axis is null, so the polar reduction covers all of `ℝ³`, for each phase
  have hz_polar : ∀ τ : ℝ, (∫⁻ z : UnforcedLeray.Space, gAx R c f τ z ^ (2 : ℝ)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ t : ℝ,
        ENNReal.ofReal ρ * gAx R c f τ (ptOf ρ t) ^ (2 : ℝ) := by
    intro τ
    have hH : Measurable (fun y : UnforcedLeray.Space => gAx R c f τ y ^ (2 : ℝ)) :=
      (hgm.comp (measurable_const.prodMk measurable_id)).pow_const _
    have hHax : ∀ y y' : UnforcedLeray.Space, hRad y = hRad y' → y 2 = y' 2 →
        gAx R c f τ y ^ (2 : ℝ) = gAx R c f τ y' ^ (2 : ℝ) := fun y y' h1 h2 => by
      rw [hax τ y y' h1 h2]
    have hpr := hP (fun y => gAx R c f τ y ^ (2 : ℝ)) hH hHax 0 le_rfl
    have hae : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space),
        z ∈ {y : UnforcedLeray.Space | (0 : ℝ) < hRad y} := by
      rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) axisNull_holds
      exact le_antisymm (not_lt.1 hz) (Real.sqrt_nonneg _)
    have hfull : (∫⁻ z : UnforcedLeray.Space, gAx R c f τ z ^ (2 : ℝ)) =
        ∫⁻ z in {y : UnforcedLeray.Space | (0 : ℝ) < hRad y}, gAx R c f τ z ^ (2 : ℝ) := by
      rw [Measure.restrict_eq_self_of_ae_mem hae]
    rw [hfull, hpr]
  -- Step 2: the `τ`-integral by `ChartChange` with `lo = 0`
  have hΘm : Measurable (fun u : ℝ × ℝ × ℝ => gAx R c f u.1 (ptOf u.2.1 u.2.2) ^ (2 : ℝ)) :=
    (hgm.comp (measurable_fst.prodMk (cs_ptOf_meas.comp measurable_snd))).pow_const _
  have hperΘ : ∀ (τ ρ t : ℝ), gAx R c f (τ + 2 * c / R) (ptOf ρ t) ^ (2 : ℝ) =
      gAx R c f τ (ptOf ρ t) ^ (2 : ℝ) := fun τ ρ t => by rw [hper]
  have hCres := hC R c 0 hR hc le_rfl (fun τ ρ t => gAx R c f τ (ptOf ρ t) ^ (2 : ℝ))
    hΘm hperΘ
  beta_reduce at hCres
  refine (lintegral_congr fun τ => hz_polar τ).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCres]
  -- Step 3: the chart set is `{0 < s}` and the chart identity holds on the cell
  have hSet : MeasurableSet {x : Chart | 0 < x.1 ∧ (0 : ℝ) < R / Real.sqrt x.1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_const.div (cs_sqrt_meas.comp measurable_fst)))
  have hFm : Measurable (fun x : Chart =>
      ENNReal.ofReal (x.1 ^ (2 : ℝ)) * ENNReal.ofReal
        (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ)) :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _))).mul hGm
  have hAS := hS c (-1 / 2) (-2) _ hFm
  rw [show (-1 / 2 : ℝ) + -2 = -5 / 2 by norm_num] at hAS
  beta_reduce at hAS
  have hset : (∫⁻ x in {x : Chart | 0 < x.1 ∧ (0 : ℝ) < R / Real.sqrt x.1},
        gAx R c f (chartTau R x) (ptOf (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) ^ (2 : ℝ)
          ∂(ageμ c (-5 / 2))) =
      ∫⁻ x, ENNReal.ofReal (x.1 ^ (2 : ℝ)) * ENNReal.ofReal
        (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ) ∂(ageμ c (-5 / 2)) := by
    rw [← lintegral_indicator hSet]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_ageμ_mem hc (-5 / 2)] with x hx
    have hs : 0 < x.1 := hx.1
    have hq : x.2.1 ∈ Ico (-c / 2) (c / 2) := hx.2.1
    have hsq : 0 < R / Real.sqrt x.1 := div_pos hR (Real.sqrt_pos.2 hs)
    have hmem : x ∈ {x : Chart | 0 < x.1 ∧ (0 : ℝ) < R / Real.sqrt x.1} := ⟨hs, hsq⟩
    rw [Set.indicator_of_mem hmem]
    have hg : gAx R c f (chartTau R x) (chartY R x) =
        ENNReal.ofReal (x.1 * UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) := by
      unfold gAx
      rw [cs_chartOf_chartY R c hR hc x hs hq]
    change gAx R c f (chartTau R x) (chartY R x) ^ (2 : ℝ) = _
    rw [hg, ENNReal.ofReal_mul hs.le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hset, hAS]
  -- Step 4: the age shift `s^{-2}` cancels `s²` on the cell
  have hcancel : (∫⁻ x, ENNReal.ofReal (x.1 ^ (-2 : ℝ)) * (ENNReal.ofReal (x.1 ^ (2 : ℝ)) *
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ))
          ∂(ageμ c (-1 / 2))) =
      ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ)
        ∂(ageμ c (-1 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_ageμ_mem hc (-1 / 2)] with x hx
    have hs : 0 < x.1 := hx.1
    have hp : x.1 ^ (-2 : ℝ) * x.1 ^ (2 : ℝ) = 1 := by
      rw [← Real.rpow_add hs]
      norm_num
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), hp, ENNReal.ofReal_one,
      one_mul]
  rw [hcancel]
  -- Step 5: the constants `2π · R c`
  have e : 2 * Real.pi * R * c = 2 * Real.pi * (R * c) := by ring
  rw [e, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
