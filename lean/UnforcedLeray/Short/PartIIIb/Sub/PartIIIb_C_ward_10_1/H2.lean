import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H1

/-!
# Helpers for `wardX0YoungL2_proved` (2): the axisymmetric transfer field and `sep:young`

Source of record: `the November 2 reference manuscript` (73 pages),
2666-2689 (chart, lift identity), 3631-3647 (`sep:young`), 4194-4196.

For a scalar `N(τ, y)` the field `w10Fn N = 1_{ϱ ≥ R√ν} N(τ, meridPt y) e_z` is axisymmetric
swirl-free by construction, its chart coefficient is `s^{-1/2} N` at the chart points, and
`ChartYoungTransport` together with `sep:young` (`p = q = 2`, `b = 1`) bounds its young chart norm.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The transfer field `1_{ϱ ≥ R√ν} N(τ, meridPt y) e_z`. -/
def w10Fn (R ν : ℝ) (N : ℝ → Space → ℝ) (τ : ℝ) (y : Space) : Space :=
  (if R * Real.sqrt ν ≤ ϱ y then N τ (meridPt y) else 0) • coordinateVector 2

theorem w10_mp0 (y : Space) : (meridPt y) 0 = ϱ y := by simp [meridPt]
theorem w10_mp1 (y : Space) : (meridPt y) 1 = 0 := by simp [meridPt]
theorem w10_mp2 (y : Space) : (meridPt y) 2 = y 2 := by simp [meridPt]

theorem w10_meridPt_idem (y : Space) : meridPt (meridPt y) = meridPt y := by
  have h := w10_varrho_meridPt y
  ext i
  fin_cases i
  · show (meridPt (meridPt y)) 0 = (meridPt y) 0
    rw [w10_mp0, w10_mp0, h]
  · show (meridPt (meridPt y)) 1 = (meridPt y) 1
    rw [w10_mp1, w10_mp1]
  · show (meridPt (meridPt y)) 2 = (meridPt y) 2
    rw [w10_mp2, w10_mp2]

theorem w10Fn_axi (R ν : ℝ) (N : ℝ → Space → ℝ) : AxiNoSwirl (w10Fn R ν N) := by
  intro τ y _ _
  have hmm := w10_meridPt_idem y
  have hϱ := w10_varrho_meridPt y
  have hc : (R * Real.sqrt ν ≤ ϱ (meridPt y)) ↔ (R * Real.sqrt ν ≤ ϱ y) := by rw [hϱ]
  have key : ∀ a : ℝ, (a • coordinateVector 2 : Space) 0 = 0 ∧ (a • coordinateVector 2 : Space) 2 = a := by
    intro a
    simp [coordinateVector]
  rw [frameL_apply]
  simp only [w10Fn, hmm, hc]
  rw [(key _).1, (key _).2]
  simp

theorem w10_measurable_meridPt : Measurable meridPt := by
  have : Measurable fun y : Space => (![ϱ y, 0, y 2] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i
    · exact continuous_ϱ.measurable
    · exact measurable_const
    · exact (EuclideanSpace.proj (2 : Fin 3)).continuous.measurable
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

theorem w10Fn_measurable (R ν : ℝ) {N : ℝ → Space → ℝ}
    (hN : Measurable (fun x : ℝ × Space => N x.1 x.2)) :
    Measurable (fun x : ℝ × Space => w10Fn R ν N x.1 x.2) := by
  unfold w10Fn
  refine Measurable.smul_const ?_ _
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (continuous_ϱ.measurable.comp measurable_snd)
  · exact hN.comp (measurable_fst.prodMk (w10_measurable_meridPt.comp measurable_snd))

theorem w10Fn_periodic (R ν P : ℝ) {N : ℝ → Space → ℝ} (hN : ∀ τ y, N (τ + P) y = N τ y)
    (τ : ℝ) (y : Space) : w10Fn R ν N (τ + P) y = w10Fn R ν N τ y := by
  simp only [w10Fn, hN]

theorem w10_chartY_meridPt {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    meridPt (NearInst.chartY R q) = NearInst.chartY R q := by
  have h := wyl_ϱ_chartY hR hs
  ext i
  fin_cases i
  · show (meridPt (NearInst.chartY R q)) 0 = (NearInst.chartY R q) 0
    rw [w10_mp0, h]
    simp [NearInst.chartY]
  · show (meridPt (NearInst.chartY R q)) 1 = (NearInst.chartY R q) 1
    rw [w10_mp1]
    simp [NearInst.chartY]
  · show (meridPt (NearInst.chartY R q)) 2 = (NearInst.chartY R q) 2
    rw [w10_mp2]

/-- The chart coefficient of the transfer field at a young chart point. -/
theorem w10Fn_coef_norm {R ν : ℝ} (hν : 0 < ν) (hR : 0 < R) {N : ℝ → Space → ℝ}
    (hN : ∀ τ y, 0 ≤ N τ y) {q : Chart} (hs : 0 < q.1) (hq : ν * q.1 ≤ 1) :
    ‖coefOf R (w10Fn R ν N) q‖ =
      (Real.sqrt q.1)⁻¹ * N (NearInst.chartTau R q) (NearInst.chartY R q) := by
  have hc := wyl_young_ϱ hν hR hs hq
  have hm := w10_chartY_meridPt hR hs
  unfold coefOf w10Fn
  rw [if_pos hc, hm]
  have h02 : ∀ a : ℝ, (a • coordinateVector 2 : Space) 0 = 0 ∧ (a • coordinateVector 2 : Space) 2 = a := by
    intro a
    simp [coordinateVector]
  rw [(h02 _).1, (h02 _).2, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  congr 1
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.sqrt_sq_eq_abs, abs_of_nonneg (hN _ _)]

/-- The young chart reading is dominated by the chart coefficient of the transfer field. -/
theorem w10_read_le_coef {R ν : ℝ} (hν : 0 < ν) (hR : 0 < R) {N : ℝ → Space → ℝ}
    (hN : ∀ τ y, 0 ≤ N τ y) {F : ℝ → Space → Space}
    (hF : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖F τ y‖ ≤ N τ y) (q : Chart) :
    wardYoungRead ν R F q ≤
      (wardYoungSet ν).indicator (fun q => ‖coefOf R (w10Fn R ν N) q‖) q := by
  by_cases hq : ν * q.1 ≤ 1
  · have hqS : q ∈ wardYoungSet ν := hq
    rw [indicator_of_mem hqS]
    rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos F hs]
      exact norm_nonneg _
    · rw [wyl_youngRead_of_young F hq, w10Fn_coef_norm hν hR hN hs hq]
      exact mul_le_mul_of_nonneg_left (hF _ _ (wyl_young_ϱ hν hR hs hq)) (inv_nonneg.2 (Real.sqrt_nonneg _))
  · have hqS : q ∉ wardYoungSet ν := hq
    rw [indicator_of_notMem hqS]
    unfold wardYoungRead
    rw [indicator_of_notMem hqS]

/-- From the transport integral to the `L²` norm of the reading. -/
theorem w10_elp_le {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) {N : ℝ → Space → ℝ}
    (hN : ∀ τ y, 0 ≤ N τ y) {F : ℝ → Space → Space}
    (hF : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖F τ y‖ ≤ N τ y) :
    eLpNorm (wardYoungRead ν R F) 2 (ageμ c (-3 / 2)) ≤
      (∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) := by
  have hS : MeasurableSet {p : Chart | ν * p.1 ≤ 1} :=
    measurableSet_le (measurable_const.mul measurable_fst) measurable_const
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← lintegral_indicator hS]
  refine lintegral_mono fun q => ?_
  have hle := w10_read_le_coef hν hR hN hF q
  have h0 := wyl_youngRead_nonneg ν R F q
  by_cases hq : q ∈ {p : Chart | ν * p.1 ≤ 1}
  · rw [indicator_of_mem hq]
    have hqS : q ∈ wardYoungSet ν := hq
    rw [indicator_of_mem hqS] at hle
    have : ‖wardYoungRead ν R F q‖ₑ ≤ ‖coefOf R (w10Fn R ν N) q‖ₑ := by
      rw [Real.enorm_of_nonneg h0, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hle
    exact ENNReal.rpow_le_rpow this (by norm_num)
  · rw [indicator_of_notMem hq]
    have hqS : q ∉ wardYoungSet ν := hq
    rw [indicator_of_notMem hqS] at hle
    have : wardYoungRead ν R F q = 0 := le_antisymm hle h0
    rw [this]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete
end
