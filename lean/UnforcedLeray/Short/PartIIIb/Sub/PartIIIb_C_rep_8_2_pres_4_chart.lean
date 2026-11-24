import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Chart form of the `Y_r` norms, and the entrance column is not in `Y_{11/4}`
(organizer task `PartIII-b:C/rep/8/2/pres/4/org`)

Source of record: `the November 2 reference manuscript`.

**(a) Chart form** (source 2681-2688: "the physical space Jacobian after azimuthal integration is
`πR²s^{-5/2}ds dη` and normalized phase becomes `dq/c`"; 5134-5139 for the `Y_{11/4}` norms of
`D^jr_b`).  For a scalar density `F(τ, y)` that depends on `y` only through `(ϱ(y), y₃)` off the
axis and is `P`-periodic in `τ`, `P = 2c/R`,
`phaseLr P r F = ‖ringRead R F‖_{L^r(ringPhysμ R c)}` (`phaseLr_eq_eLpNorm_ringRead`), from
`Axi.phaseAvg_ringChart` (`Lib/Axisymmetric/RingMeasure.lean:229`).  At a level of the return
(`R = ε⁻¹`, `c = ν⁻²`, `P = 2εc`, `r = 11/4`): `phaseLr_eq_eLpNorm_ringRead_level`.  This is the
conversion of `RepairDerivBound` (`ReturnRepair/Estimates.lean:219`) and of
`IIb.ExactSplitII.energy` to the ring-chart norms used in `PresCoef.lean`.

**(b) The entrance column has infinite `Y_{11/4}` norm** (source 2346-2347: "The exact stream
lift `E_εα` is affine: its nonzero inlet is not in `Y_p`"; 2389-2390: "These assertions compare
sources, never the nonintegrable inlet states").  The inlet column `E_i = N_v e_ε`
(`Params.inlet`, `Cons/L2/BackgroundConcrete/Fields.lean:213`) has `|E_i| = √s|e_ε|` at the chart
point, and `e_ε(s, q, η) = (−ψ_η, ψ_q + ε(ψ − ηψ_η))` does not depend on `s` for `s ≤ H/4`
(`ageCutoff = 1` there).  The chart measure is `πR²c⁻¹s^{-5/2}ds dq dη`, so the `11/4`-th power of
the chart norm is at least `πR²c⁻¹∫_0^{H/4}s^{11/8-5/2}ds·∫_{cell}|e_ε(0,·)|^{11/4} = ∞`
(`∫_0 s^{-9/8} = ∞`).  `eLpNorm_ringRead_eq_top_of_young` proves this for every density bounded
below by `√s|e(q, η)|` on `0 < s ≤ s₀` with `e ≢ 0` on the cell.  Hence the `Y_{11/4}` chart norm
of `coefChgDens (L.U) (rawU Pl L) ≥ |U - U_raw| = |E_εα_bg + r_b|` is infinite whenever
`α_bg ≠ 0` (`r_b` has finite norm), and `CoefChgAt` (`PresCoef.lean:150`, second clause),
`CoefChgQuant` (`Sub/PartIII-b_C_rep_8_2_pres_4.lean`) and `CoefChgLp`
(`Sub/PartIII-b_C_rep_8_2_pres_4_2.lean`) are false at every level with `α_bg ≠ 0`.  The source
measures only the repair change `r_b` in `Y_{11/4}` (5134-5139) and the entrance change
`E_εα_bg` in `W^{j,∞}` with `|α| ≤ P_νe^{m/ν}ε` (2389, 2519-2520: "or have a larger curvature
power", 5288-5289).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## The chart point of a physical point -/

theorem measurable_chartTau_p4 (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

theorem measurable_chartY_p4 (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

theorem measurable_ringRead_p4 (R : ℝ) {F : ℝ → Space → ℝ}
    (hF : Measurable fun x : ℝ × Space => F x.1 x.2) : Measurable (ringRead R F) :=
  hF.comp ((measurable_chartTau_p4 R).prodMk (measurable_chartY_p4 R))

/-- The phase of the chart point of `(τ, y)` is `τ` (`τ = 2q/R + log s`, source 2670-2674). -/
theorem chartTau_chart_p4 {R : ℝ} (hR : 0 < R) (τ : ℝ) (y : Space) :
    NearInst.chartTau R (chart R τ y) = τ := by
  have hR' : R ≠ 0 := hR.ne'
  simp only [NearInst.chartTau, chart, phase]
  field_simp
  ring

/-- The physical point of the chart point of `y` is `y` rotated to azimuth `0`:
`(R/√s, 0, η/√s) = (ϱ(y), 0, y₃)` (source 2670-2674). -/
theorem chartY_chart_p4 {R : ℝ} (hR : 0 < R) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    NearInst.chartY R (chart R τ y) = WithLp.toLp 2 ![ϱ y, 0, y 2] := by
  have hϱ : ϱ y ≠ 0 := (ϱ_pos hy).ne'
  have hR' : R ≠ 0 := hR.ne'
  simp only [NearInst.chartY, chart]
  rw [sqrt_age hR hy]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
  · simp
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    unfold Axi.trans
    field_simp

/-! ## (a) `phaseLr` is the ring-chart norm for axisymmetric densities -/

/-- **Chart form of the `Y_r` norm** (source 2681-2688, 5134-5139): for a jointly measurable
scalar density `F(τ, y)` that is determined off the axis by its value at azimuth `0`
(`F τ y = F τ (ϱ(y), 0, y₃)`) and is `P`-periodic in `τ`, `P = 2c/R`,
`‖F‖_{Y_r} = phaseLr P r F = ‖ringRead R F‖_{L^r(ringPhysμ R c)}`. -/
theorem phaseLr_eq_eLpNorm_ringRead {R c P r : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hP : P = 2 * c / R) (hr : 0 < r) (F : ℝ → Space → ℝ)
    (hF : Measurable fun x : ℝ × Space => F x.1 x.2)
    (haxi : ∀ (τ : ℝ) (y : Space), y ∉ axis → F τ y = F τ (WithLp.toLp 2 ![ϱ y, 0, y 2]))
    (hper : ∀ (τ : ℝ) (y : Space), F (τ + P) y = F τ y) :
    phaseLr P r (fun x => F x.1 x.2) =
      eLpNorm (ringRead R F) (ENNReal.ofReal r) (ringPhysμ R c) := by
  have hP0 : 0 < P := by rw [hP]; positivity
  set G : Chart → ℝ≥0∞ := fun p => ENNReal.ofReal |ringRead R F p| ^ r with hGdef
  have hRm : Measurable (ringRead R F) := measurable_ringRead_p4 R hF
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hRm)).pow_const r
  have hGper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η)) := by
    intro s q η
    simp only [hGdef, ringRead, NearInst.chartTau, NearInst.chartY]
    have h : 2 * (q + c) / R + Real.log s = (2 * q / R + Real.log s) + P := by
      rw [hP]; ring
    rw [h, hper]
  have hin : ∀ τ : ℝ, ∫⁻ y, ENNReal.ofReal |F τ y| ^ r =
      ∫⁻ y, G (age R y, (phase R τ y, trans R y)) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_not_mem_axis] with y hy
    have hc' : (age R y, (phase R τ y, trans R y)) = chart R τ y := rfl
    simp only [hGdef, ringRead]
    rw [hc', chartTau_chart_p4 hR τ y, chartY_chart_p4 hR τ hy, ← haxi τ y hy]
  have hL : (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, ENNReal.ofReal |F τ y| ^ r =
      ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (fun τ _ => hin τ)]
    exact phaseAvg_ringChart hR hc hP G hGm hGper
  have hr0 : ENNReal.ofReal r ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr
  have henorm : (fun p => ‖ringRead R F p‖ₑ ^ r) = G := by
    funext p
    simp only [hGdef, Real.enorm_eq_ofReal_abs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le, henorm]
  unfold phaseLr
  rw [ENNReal.ofReal_inv_of_pos hP0]
  show ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, ENNReal.ofReal |F τ y| ^ r) ^ (1 / r) = _
  have h52 : (-5 / 2 : ℝ) = -(5 / 2) := by norm_num
  rw [hL, ringPhysμ, lintegral_smul_measure, lintegral_ageμ hc _ hGm, smul_eq_mul, h52]

/-- `(11/4 : ℝ≥0∞) = ofReal (11/4)`. -/
theorem ofReal_eleven_fourths : ENNReal.ofReal (11 / 4) = (11 / 4 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  simp

/-- **Chart form at a level of the return** (`R = ε⁻¹`, `c = ν⁻²`, `P = 2εc`, `r = 11/4`;
source 2666-2688, 5134-5139): `phaseLr (2εc) (11/4) F = ‖ringRead ε⁻¹ F‖_{L^{11/4}(ringPhysμ)}`
for axisymmetric, `2εc`-periodic, jointly measurable densities. -/
theorem phaseLr_eq_eLpNorm_ringRead_level (L : ReturnLevel) (F : ℝ → Space → ℝ)
    (hF : Measurable fun x : ℝ × Space => F x.1 x.2)
    (haxi : ∀ (τ : ℝ) (y : Space), y ∉ axis → F τ y = F τ (WithLp.toLp 2 ![ϱ y, 0, y 2]))
    (hper : ∀ (τ : ℝ) (y : Space), F (τ + 2 * L.ε * cOf L.ν) y = F τ y) :
    phaseLr (2 * L.ε * cOf L.ν) (11 / 4) (fun x => F x.1 x.2) =
      eLpNorm (ringRead L.ε⁻¹ F) (11 / 4) (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
  have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by
    rw [div_inv_eq_mul]; ring
  rw [phaseLr_eq_eLpNorm_ringRead (inv_pos.2 L.ε_pos) (cOf_pos L.ν_pos) hP (by norm_num) F hF
    haxi hper, ofReal_eleven_fourths]

/-! ## (b) A nonzero inlet trace is not in `Y_{11/4}` -/

/-- `∫_0^{s₀} s^{-9/8} ds = ∞` (the age integrability exponent of an `L^{11/4}` inlet state:
`11/8 - 5/2 = -9/8 < -1`, source 2346-2347, 2389-2390). -/
theorem lintegral_Ioc_rpow_neg_nine_eighths {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∫⁻ s in Ioc (0 : ℝ) s₀, ENNReal.ofReal (s ^ (-(9 / 8 : ℝ))) = ⊤ := by
  by_contra h
  have hint : IntegrableOn (fun s : ℝ => s ^ (-(9 / 8 : ℝ))) (Ioo 0 s₀) := by
    refine ⟨(measurable_id.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact lt_of_le_of_lt (lintegral_mono_set Ioo_subset_Ioc_self) (lt_top_iff_ne_top.2 h)
    · exact (ae_restrict_iff' measurableSet_Ioo).2
        (Eventually.of_forall fun s hs => Real.rpow_nonneg hs.1.le _)
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hs₀).1 hint
  norm_num at this

/-- **A density bounded below by a nonzero inlet trace has infinite `Y_{11/4}` chart norm**
(source 2346-2347: "its nonzero inlet is not in `Y_p`"; 2389-2390): if
`√s|e(q, η)| ≤ |ringRead R f (s, q, η)|` for `0 < s ≤ s₀` and `∫_{cell}|e|^{11/4} ≠ 0`, then
`‖ringRead R f‖_{L^{11/4}(ringPhysμ R c)} = ∞`.  Applied to `f = coefChgDens (L.U) (rawU Pl L)`,
`|U - U_raw| = |Σᵢαᵢ E_i + r_b|`, `E_i = N_v e_ε` with `e_ε(s, ·) = e_ε(0, ·)` for `s ≤ H/4`. -/
theorem eLpNorm_ringRead_eq_top_of_young {R c s₀ : ℝ} (hR : 0 < R) (hc : 0 < c) (hs₀ : 0 < s₀)
    (f : ℝ → Space → ℝ) (e : ℝ × ℝ → ℝ) (he : Measurable e)
    (hf : ∀ p : Chart, 0 < p.1 → p.1 ≤ s₀ → Real.sqrt p.1 * |e p.2| ≤ |ringRead R f p|)
    (hpos : ∫⁻ x in qCell c, ENNReal.ofReal |e x| ^ (11 / 4 : ℝ) ≠ 0) :
    eLpNorm (ringRead R f) (11 / 4) (ringPhysμ R c) = ⊤ := by
  set r : ℝ := 11 / 4 with hrdef
  have hr : 0 < r := by norm_num [hrdef]
  -- the measurable minorant
  set g : ℝ → ℝ≥0∞ := (Ioc (0 : ℝ) s₀).indicator fun s => ENNReal.ofReal (s ^ (11 / 8 : ℝ))
    with hgdef
  set E : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |e x| ^ r with hEdef
  have hgm : Measurable g :=
    ((measurable_ofReal_rpow (11 / 8 : ℝ))).indicator measurableSet_Ioc
  have hEm : Measurable E :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp he)).pow_const r
  have hle : ∀ p : Chart, g p.1 * E p.2 ≤ ‖ringRead R f p‖ₑ ^ r := by
    intro p
    by_cases hp : p.1 ∈ Ioc (0 : ℝ) s₀
    · have hs : 0 < p.1 := hp.1
      have hgp : g p.1 = ENNReal.ofReal (p.1 ^ (11 / 8 : ℝ)) := by
        simp only [hgdef, Set.indicator_of_mem hp]
      have hsq : ENNReal.ofReal (p.1 ^ (11 / 8 : ℝ)) = ENNReal.ofReal (Real.sqrt p.1) ^ r := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hr.le, sqrt_rpow hs.le]
        norm_num [hrdef]
      simp only [hEdef]
      rw [hgp, hsq, ← ENNReal.mul_rpow_of_nonneg _ _ hr.le,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.enorm_eq_ofReal_abs]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hf p hs hp.2)) hr.le
    · simp only [hgdef, Set.indicator_of_notMem hp, zero_mul, zero_le]
  -- the integral of the minorant is infinite
  have hK : ∫⁻ x, E x ∂(UnforcedLeray.Cyl.avgμ c) ≠ 0 := by
    rw [UnforcedLeray.Cyl.avgμ, lintegral_smul_measure, smul_eq_mul, UnforcedLeray.Cyl.cellμ]
    refine mul_ne_zero ?_ ?_
    · rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hc
    · rw [← qCell_eq_cell]; exact hpos
  have hg_int : ∫⁻ s, g s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))) = ⊤ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_ofReal_rpow _) hgm]
    have hind : (fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))) * g =
        (Ioc (0 : ℝ) s₀).indicator fun s =>
          ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ENNReal.ofReal (s ^ (11 / 8 : ℝ)) := by
      funext s
      by_cases hs : s ∈ Ioc (0 : ℝ) s₀
      · simp only [Pi.mul_apply, hgdef, Set.indicator_of_mem hs]
      · simp only [Pi.mul_apply, hgdef, Set.indicator_of_notMem hs, mul_zero]
    rw [hind, lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 Ioc_subset_Ioi_self]
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun s => ENNReal.ofReal (s ^ (-(9 / 8 : ℝ))))
      (fun s hs => by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _), ← Real.rpow_add hs.1]
        norm_num)]
    exact lintegral_Ioc_rpow_neg_nine_eighths hs₀
  have hprod : ∫⁻ p, g p.1 * E p.2 ∂(ageμ c (-5 / 2)) = ⊤ := by
    rw [ageμ, lintegral_prod (fun p : ℝ × (ℝ × ℝ) => g p.1 * E p.2)
      ((hgm.comp measurable_fst).mul (hEm.comp measurable_snd)).aemeasurable]
    simp only [lintegral_const_mul _ hEm]
    rw [lintegral_mul_const _ hgm, hg_int, ENNReal.top_mul hK]
  have hint : ∫⁻ p, ‖ringRead R f p‖ₑ ^ r ∂(ringPhysμ R c) = ⊤ := by
    rw [ringPhysμ, lintegral_smul_measure, smul_eq_mul]
    have h1 : ∫⁻ p, ‖ringRead R f p‖ₑ ^ r ∂(ageμ c (-5 / 2)) = ⊤ :=
      top_le_iff.1 (hprod ▸ lintegral_mono hle)
    rw [h1]
    refine ENNReal.mul_top ?_
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have h0 : (11 / 4 : ℝ≥0∞) ≠ 0 := by norm_num
  have htop : (11 / 4 : ℝ≥0∞) ≠ ⊤ := by
    rw [← ofReal_eleven_fourths]; exact ENNReal.ofReal_ne_top
  have hreal : (11 / 4 : ℝ≥0∞).toReal = r := by
    rw [← ofReal_eleven_fourths, ENNReal.toReal_ofReal (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 htop, hreal, hint]
  exact ENNReal.top_rpow_of_pos (by positivity)

/-! ## (c) Sup bounds at chart points: `|V| = √s|v|` for fields without hoop component

Source 2715-2725 (`v = s^{-1/2}V`, `sup √s W|v| ≤ P_ν`; `NearInst.SplitMultBound`,
`NearInst/Targets.lean:140`, states it for `IIIa.chartCoeff R V`).  At the chart point
`y = (R/√s, 0, η/√s)` (azimuth `0`) the ring lifts `N_v b` (`U_raw` off the axis, the inlet
columns `E_i`) have zero second Cartesian component, so `|V| = √s|v| ≤ √s W|v|`. -/

theorem chartY_one_p4 (R : ℝ) (p : Chart) : NearInst.chartY R p 1 = 0 := by
  simp [NearInst.chartY]

theorem chartY_not_mem_axis_p4 {R : ℝ} (hR : 0 < R) {p : Chart} (hp : 0 < p.1) :
    NearInst.chartY R p ∉ axis := by
  intro h
  have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hp).ne'
  exact hne (by simpa [NearInst.chartY] using h.1)

/-- A ring lift has zero second Cartesian component in the half-plane `y₁ = 0`. -/
theorem Nv_apply_one_p4 (R : ℝ) (b : Chart → Merid) (τ : ℝ) {y : Space} (hy : y 1 = 0) :
    Nv R b τ y 1 = 0 := by
  simp [Nv, frameL_apply, eR, hor, hy, coordinateVector_apply]

/-- `|V| = √s|v|` at a chart point when the hoop component vanishes there (`v = chartCoeff`). -/
theorem norm_eq_sqrt_mul_chartCoeff_p4 (R : ℝ) (V : ℝ → Space → Space) {p : Chart}
    (hp : 0 < p.1) (h1 : V (NearInst.chartTau R p) (NearInst.chartY R p) 1 = 0) :
    ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖ =
      Real.sqrt p.1 * ‖UnforcedLeray.Short.IIIa.chartCoeff R V p‖ := by
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  set w := V (NearInst.chartTau R p) (NearInst.chartY R p) with hw
  have hcc : UnforcedLeray.Short.IIIa.chartCoeff R V p =
      (Real.sqrt p.1)⁻¹ • (!₂[w 0, w 2] : Merid) := rfl
  rw [hcc, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Fin.sum_univ_three, Fin.sum_univ_two, h1]
  simp

theorem one_le_transWeight_p4 {mZ : ℝ} (hmZ : 0 ≤ mZ) (p : Chart) :
    1 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)

/-- **`|V| ≤ √s W|v|` at chart points** (source 2715-2725), for a field with zero hoop component
at azimuth `0`. -/
theorem norm_le_of_chartCoeff_p4 (R : ℝ) {mZ : ℝ} (hmZ : 0 ≤ mZ) (V : ℝ → Space → Space)
    {p : Chart} (hp : 0 < p.1) (h1 : V (NearInst.chartTau R p) (NearInst.chartY R p) 1 = 0) :
    ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖ ≤
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
        ‖UnforcedLeray.Short.IIIa.chartCoeff R V p‖ := by
  rw [norm_eq_sqrt_mul_chartCoeff_p4 R V hp h1, mul_right_comm]
  exact le_mul_of_one_le_right (by positivity) (one_le_transWeight_p4 hmZ p)

/-- `U_raw` has zero hoop component at the chart points of its level (off the axis
`U_raw = N_v b_raw`, `Params.raw_eq_off_axis`, source 2076-2077, 5200). -/
theorem rawU_chart_one_p4 (Pl : UnforcedLeray.Blueprint.Planar.PlanarData) (L : ReturnLevel)
    {p : Chart} (hp : 0 < p.1) :
    rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) 1 = 0 := by
  have hax := chartY_not_mem_axis_p4 (inv_pos.2 L.ε_pos) hp
  rw [rawU, (L.params Pl).raw_eq_off_axis _ _ hax]
  exact Nv_apply_one_p4 _ _ _ (chartY_one_p4 _ p)

/-- The inlet columns `E_i = N_v e_ε` have zero hoop component in the half-plane `y₁ = 0`
(`Params.inlet`, source 2347-2369). -/
theorem inlet_chart_one_p4 (P : UnforcedLeray.Cons.C03.Concrete.Params) (i : Fin 2) (τ : ℝ)
    (R : ℝ) (p : Chart) : P.inlet i τ (NearInst.chartY R p) 1 = 0 :=
  Nv_apply_one_p4 _ _ _ (chartY_one_p4 R p)

end UnforcedLeray.Short.PartIIIb.Concrete
