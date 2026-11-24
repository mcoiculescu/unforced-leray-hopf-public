import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1
import UnforcedLeray.Short.PartIIb.Sub.TrainCloseCell
import UnforcedLeray.Units.B0592
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Part II-b, task `PartII-b:F1/1`: cylinder weighted Biot–Savart operator bound and compactness

Proves `cylWeightedKernelStep_proof : CylWeightedKernelStep` (SP lines 2117–2118, 2133–2137).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.B0579

/-! ## 1. Real Hilbert–Schmidt integral operators via `ExternalInputs.kernelOperator` -/

section RealHS

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem memLp_ofReal_comp {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (fun z => (k z : ℂ)) 2 (μ.prod μ) :=
  Complex.ofRealCLM.comp_memLp' hk

private theorem eLpNorm_ofReal_comp (k : α × α → ℝ) :
    eLpNorm (fun z => (k z : ℂ)) 2 (μ.prod μ) = eLpNorm k 2 (μ.prod μ) :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun z => Complex.norm_real (k z))

variable [SFinite μ]

/-- Real integral operator on `L²(μ)` with square-integrable kernel `k ∈ L²(μ ⊗ μ)`. -/
def realKernelOperator {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Complex.reCLM.compLpL 2 μ).comp
    (((ExternalInputs.kernelOperator (memLp_ofReal_comp hk)).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 μ))

theorem isCompactOperator_realKernelOperator {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    IsCompactOperator (realKernelOperator hk) := by
  have hC : IsCompactOperator
      ((ExternalInputs.kernelOperator (memLp_ofReal_comp hk)).restrictScalars ℝ) :=
    ExternalInputs.isCompactOperator_kernelOperator (memLp_ofReal_comp hk)
  exact (hC.comp_clm (Complex.ofRealCLM.compLpL 2 μ)).clm_comp (Complex.reCLM.compLpL 2 μ)

theorem coeFn_realKernelOperator {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
    (realKernelOperator hk f : α → ℝ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂μ := by
  set kC : α × α → ℂ := fun z => (k z : ℂ)
  set toC := Complex.ofRealCLM.compLpL 2 μ
  set toR := Complex.reCLM.compLpL 2 μ
  set TC := ExternalInputs.kernelOperator (memLp_ofReal_comp hk)
  have h1 : (realKernelOperator hk f : α → ℝ) =ᵐ[μ] fun x => (TC (toC f) x).re :=
    ContinuousLinearMap.coeFn_compLpL Complex.reCLM (TC (toC f))
  have h2 : (TC (toC f) : α → ℂ) =ᵐ[μ] fun x => ∫ y, kC (x, y) * toC f y ∂μ :=
    ExternalInputs.coeFn_kernelOperator (memLp_ofReal_comp hk) (toC f)
  have hfC : (toC f : α → ℂ) =ᵐ[μ] fun y => (f y : ℂ) :=
    ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]
  have hint : ∫ y, kC (x, y) * toC f y ∂μ = ∫ y, ((k (x, y) * f y : ℝ) : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfC] with y hy
    simp [kC, hy]
  rw [hint, integral_complex_ofReal, Complex.ofReal_re]

theorem norm_realKernelOperator_le {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    ‖realKernelOperator hk‖ ≤ (eLpNorm k 2 (μ.prod μ)).toReal := by
  refine ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg fun f => ?_
  have hre : ‖Complex.reCLM.compLpL 2 μ‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le Complex.reCLM).trans Complex.reCLM_norm.le
  have hof : ‖Complex.ofRealCLM.compLpL 2 μ‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le Complex.ofRealCLM).trans Complex.ofRealCLM_norm.le
  have hTC : ‖ExternalInputs.kernelOperator (memLp_ofReal_comp hk)‖ ≤
      (eLpNorm k 2 (μ.prod μ)).toReal := by
    rw [← eLpNorm_ofReal_comp k]
    exact ExternalInputs.norm_kernelOperator_le (memLp_ofReal_comp hk)
  have hstep1 : ‖realKernelOperator hk f‖ ≤
      ‖Complex.reCLM.compLpL 2 μ‖ *
        ‖ExternalInputs.kernelOperator (memLp_ofReal_comp hk)
          (Complex.ofRealCLM.compLpL 2 μ f)‖ :=
    (Complex.reCLM.compLpL 2 μ).le_opNorm _
  have hstep2 : ‖ExternalInputs.kernelOperator (memLp_ofReal_comp hk)
        (Complex.ofRealCLM.compLpL 2 μ f)‖ ≤
      ‖ExternalInputs.kernelOperator (memLp_ofReal_comp hk)‖ *
        ‖Complex.ofRealCLM.compLpL 2 μ f‖ :=
    (ExternalInputs.kernelOperator (memLp_ofReal_comp hk)).le_opNorm _
  have hstep3 : ‖Complex.ofRealCLM.compLpL 2 μ f‖ ≤ 1 * ‖f‖ :=
    ((Complex.ofRealCLM.compLpL 2 μ).le_opNorm f).trans (by gcongr)
  calc ‖realKernelOperator hk f‖
      ≤ 1 * ‖ExternalInputs.kernelOperator (memLp_ofReal_comp hk)
          (Complex.ofRealCLM.compLpL 2 μ f)‖ :=
        hstep1.trans (by gcongr)
    _ ≤ 1 * ((eLpNorm k 2 (μ.prod μ)).toReal * (1 * ‖f‖)) := by
        gcongr
        exact hstep2.trans (by gcongr)
    _ = (eLpNorm k 2 (μ.prod μ)).toReal * ‖f‖ := by ring

end RealHS

/-! ## 2. Periodic cell wrapping and the radius-`r` near/far kernel split -/

theorem cell_eq_cylCell (c : ℝ) : B0579.cell c = Cyl.cell c := by
  simp only [B0579.cell, Cyl.cell, neg_div]

/-- Wrapping the horizontal coordinate into `[-c/2, c/2)`: `wrapPlane c (q, η) = (qwrap c q, η)`. -/
def wrapPlane (c : ℝ) (z : Plane) : Plane := (qwrap c z.1, z.2)

theorem wrapPlane_mem_cell {c : ℝ} (hc : 0 < c) (z : Plane) : wrapPlane c z ∈ B0579.cell c :=
  ⟨qwrap_mem_Ico hc z.1, mem_univ _⟩

theorem wrapPlane_of_mem_cell {c : ℝ} (hc : 0 < c) {z : Plane} (hz : z ∈ B0579.cell c) :
    wrapPlane c z = z := by
  have h1 : -(c / 2) ≤ z.1 := hz.1.1
  have h2 : z.1 < c / 2 := hz.1.2
  have hfl : ⌊(z.1 + c / 2) / c⌋ = 0 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · simp only [Int.cast_zero]
      exact div_nonneg (by linarith) hc.le
    · simp only [Int.cast_zero, zero_add]
      rw [div_lt_one hc]
      linarith
  ext
  · simp [wrapPlane, qwrap, hfl]
  · rfl

theorem isPeriodic_wrapPlane {c : ℝ} (hc : 0 < c) : Cyl.IsPeriodic c (wrapPlane c) := by
  intro z
  have hq : (z.1 + c + c / 2) / c = (z.1 + c / 2) / c + 1 := by
    have : c ≠ 0 := hc.ne'
    field_simp
    ring
  ext
  · simp only [wrapPlane, qwrap, hq, Int.floor_add_one, Int.cast_add, Int.cast_one]
    ring
  · rfl

theorem measurable_wrapPlane (c : ℝ) : Measurable (wrapPlane c) := by
  unfold wrapPlane qwrap
  refine (measurable_fst.sub ?_).prodMk measurable_snd
  exact measurable_const.mul ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp
    (Int.measurable_floor.comp ((measurable_fst.add_const _).div_const _)))

theorem bsKernel_wrapPlane (c : ℝ) (z : Plane) :
    Cyl.bsKernel c (wrapPlane c z) = Cyl.bsKernel c z := by
  have h : wrapPlane c z = (z.1 + ((-⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) * c, z.2) := by
    ext
    · simp [wrapPlane, qwrap]; ring
    · rfl
  rw [h]
  exact (Cyl.isPeriodic_bsKernel c).add_int_mul _ z

/-- Near cylinder Biot–Savart kernel at radius `r`: `K_c(z) 1_{‖wrapPlane c z‖ < r}`. -/
def kNearR (c r : ℝ) (z : Plane) : Cyl.Vec2 :=
  if ‖wrapPlane c z‖ < r then Cyl.bsKernel c z else 0

/-- Far cylinder Biot–Savart kernel at radius `r`: `K_c(z) 1_{‖wrapPlane c z‖ ≥ r}`. -/
def kFarR (c r : ℝ) (z : Plane) : Cyl.Vec2 :=
  if r ≤ ‖wrapPlane c z‖ then Cyl.bsKernel c z else 0

theorem kNearR_add_kFarR (c r : ℝ) (z : Plane) :
    kNearR c r z + kFarR c r z = Cyl.bsKernel c z := by
  unfold kNearR kFarR
  rcases lt_or_ge ‖wrapPlane c z‖ r with h | h
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mpr h]

theorem isPeriodic_kNearR {c : ℝ} (hc : 0 < c) (r : ℝ) : Cyl.IsPeriodic c (kNearR c r) := by
  intro z
  simp only [kNearR, isPeriodic_wrapPlane hc z, Cyl.isPeriodic_bsKernel c z]

theorem isPeriodic_kFarR {c : ℝ} (hc : 0 < c) (r : ℝ) : Cyl.IsPeriodic c (kFarR c r) := by
  intro z
  simp only [kFarR, isPeriodic_wrapPlane hc z, Cyl.isPeriodic_bsKernel c z]

theorem measurable_kNearR (c r : ℝ) : Measurable (kNearR c r) :=
  Measurable.ite (measurableSet_lt (measurable_norm.comp (measurable_wrapPlane c)) measurable_const)
    (Cyl.measurable_bsKernel c) measurable_const

theorem measurable_kFarR (c r : ℝ) : Measurable (kFarR c r) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_norm.comp (measurable_wrapPlane c)))
    (Cyl.measurable_bsKernel c) measurable_const

/-- Pointwise far bound `‖kFarR c r z‖ ≤ r⁻¹ + 1` on the whole plane (`c ≥ 1`, `r > 0`). -/
theorem norm_kFarR_le {c r : ℝ} (hc : 1 ≤ c) (hr : 0 < r) (z : Plane) :
    ‖kFarR c r z‖ ≤ r⁻¹ + 1 := by
  unfold kFarR
  split_ifs with h
  · have hc0 : 0 < c := by linarith
    have hmem : wrapPlane c z ∈ B0579.cell c := wrapPlane_mem_cell hc0 z
    have hq : |(wrapPlane c z).1| ≤ c / 2 := by
      rw [abs_le]
      exact ⟨hmem.1.1, hmem.1.2.le⟩
    have hne : wrapPlane c z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      linarith
    rw [← bsKernel_wrapPlane c z]
    have h1 := Cyl.norm_bsKernel_le hc hq hne
    have h2 : r ≤ Real.sqrt ((wrapPlane c z).1 ^ 2 + (wrapPlane c z).2 ^ 2) :=
      h.trans (Cyl.sup_norm_le_euclid _)
    have h3 : (Real.sqrt ((wrapPlane c z).1 ^ 2 + (wrapPlane c z).2 ^ 2))⁻¹ ≤ r⁻¹ :=
      inv_anti₀ hr h2
    linarith
  · rw [norm_zero]
    positivity

theorem norm_kFarR_coord_le {c r : ℝ} (hc : 1 ≤ c) (hr : 0 < r) (z : Plane) (i : Fin 2) :
    |kFarR c r z i| ≤ r⁻¹ + 1 := by
  have h1 := PiLp.norm_apply_le (kFarR c r z) i
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (norm_kFarR_le hc hr z)

theorem kNearR_eq_indicator_on_cell {c r : ℝ} (hc : 0 < c) {y : Plane} (hy : y ∈ B0579.cell c) :
    kNearR c r y = (B0579.cell c ∩ Metric.ball 0 r).indicator (Cyl.bsKernel c) y := by
  rw [kNearR, wrapPlane_of_mem_cell hc hy]
  by_cases hb : ‖y‖ < r
  · have hm : y ∈ B0579.cell c ∩ Metric.ball 0 r := ⟨hy, by simpa [mem_ball_zero_iff] using hb⟩
    simp [hb, hm]
  · have hm : y ∉ B0579.cell c ∩ Metric.ball 0 r := fun h =>
      hb (by simpa [mem_ball_zero_iff] using h.2)
    simp [hb, hm]

theorem norm_kNearR_le_kNear_on_cell {c r : ℝ} (hc : 0 < c) (hr : r ≤ 1) {y : Plane}
    (hy : y ∈ B0579.cell c) :
    ‖kNearR c r y‖ₑ ≤ ‖Cyl.kNear c y‖ₑ := by
  rw [kNearR_eq_indicator_on_cell hc hy, Cyl.kNear, ← cell_eq_cylCell]
  by_cases hb : y ∈ B0579.cell c ∩ Metric.ball 0 r
  · have hb1 : y ∈ B0579.cell c ∩ Metric.ball 0 1 :=
      ⟨hb.1, Metric.ball_subset_ball hr hb.2⟩
    rw [indicator_of_mem hb, indicator_of_mem hb1]
  · rw [indicator_of_notMem hb, enorm_zero]
    exact zero_le

/-- Universal `L¹(cell)` bound on `Cyl.kNear c` for `c ≥ 1`. -/
def nearKernelConst : ℝ := Classical.choose Cyl.bsKernel_split

theorem nearKernelConst_nonneg : 0 ≤ nearKernelConst :=
  (Classical.choose_spec Cyl.bsKernel_split).1

theorem lintegral_kNear_le {c : ℝ} (hc : 1 ≤ c) :
    ∫⁻ y in B0579.cell c, ‖Cyl.kNear c y‖ₑ ≤ ENNReal.ofReal nearKernelConst := by
  rw [cell_eq_cylCell]
  exact ((Classical.choose_spec Cyl.bsKernel_split).2 c hc).1

theorem lintegral_kNearR_le {c r : ℝ} (hc : 1 ≤ c) (hr : r ≤ 1) :
    ∫⁻ y in B0579.cell c, ‖kNearR c r y‖ₑ ≤ ENNReal.ofReal nearKernelConst := by
  have hc0 : 0 < c := by linarith
  refine (setLIntegral_mono' (B0579.measurableSet_cell c) fun y hy =>
    norm_kNearR_le_kNear_on_cell hc0 hr hy).trans (lintegral_kNear_le hc)

/-- Dominated convergence `∫_{cell c} ‖kNearR c (rad n)‖ → 0` as `n → ∞`. -/
theorem tendsto_lintegral_kNearR {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun n : ℕ => ∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ) atTop (𝓝 0) := by
  have hc0 : 0 < c := by linarith
  have hfin : ∫⁻ y in B0579.cell c, ‖Cyl.kNear c y‖ₑ ≠ ∞ :=
    ((lintegral_kNear_le hc).trans_lt ENNReal.ofReal_lt_top).ne
  have h0 : ∀ᵐ y ∂(volume.restrict (B0579.cell c)), y ≠ 0 :=
    ae_restrict_of_ae (by rw [ae_iff]; simp [measure_singleton])
  have hdom : ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict (B0579.cell c)),
      ‖kNearR c (B0061.rad n) y‖ₑ ≤ ‖Cyl.kNear c y‖ₑ := fun n =>
    ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun y hy =>
      norm_kNearR_le_kNear_on_cell hc0 (B0061.rad_le_one n) hy
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := volume.restrict (B0579.cell c))
    (F := fun n y => ‖kNearR c (B0061.rad n) y‖ₑ)
    (f := fun _ => 0)
    (bound := fun y => ‖Cyl.kNear c y‖ₑ)
    (fun n => (measurable_kNearR c (B0061.rad n)).enorm)
    hdom hfin
    (by
      filter_upwards [h0, ae_restrict_mem (B0579.measurableSet_cell c)] with y hy0 hyc
      have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hyp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hr : B0061.rad n < ‖y‖ := by
        refine lt_of_le_of_lt ?_ hN
        unfold B0061.rad
        gcongr
      simp [kNearR, wrapPlane_of_mem_cell hc0 hyc, not_lt.mpr hr.le])
  simpa using h

/-! ## 3. Periodic extension, near/far velocity split, and `L²(cell)` Young estimate -/

/-- Periodic extension of `f : Plane → ℝ` from `cell c` to `Plane`. -/
def extPer (c : ℝ) (f : Plane → ℝ) (z : Plane) : ℝ := f (wrapPlane c z)

theorem isPeriodic_extPer {c : ℝ} (hc : 0 < c) (f : Plane → ℝ) :
    Cyl.IsPeriodic c (extPer c f) := fun z => by
  simp only [extPer, isPeriodic_wrapPlane hc z]

theorem extPer_of_mem_cell {c : ℝ} (hc : 0 < c) (f : Plane → ℝ) {y : Plane}
    (hy : y ∈ B0579.cell c) :
    extPer c f y = f y := by
  rw [extPer, wrapPlane_of_mem_cell hc hy]

theorem stronglyMeasurable_extPer (c : ℝ) {f : Plane → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (extPer c f) :=
  hf.comp_measurable (measurable_wrapPlane c)

theorem eLpNorm_extPer_cellμ {c : ℝ} (hc : 0 < c) (f : Plane → ℝ) (p : ℝ≥0∞) :
    eLpNorm (extPer c f) p (Cyl.cellμ c) = eLpNorm f p (Cyl.cellμ c) := by
  refine eLpNorm_congr_ae ?_
  rw [Cyl.cellμ, ← cell_eq_cylCell]
  exact ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun y hy =>
    extPer_of_mem_cell hc f hy

theorem eLpNorm_cell_le_norm {c m : ℝ} (hm : 0 ≤ m) (f : Xmc c m) :
    eLpNorm (f : Plane → ℝ) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal ‖f‖ := by
  apply B0592.ennreal_le_of_sq_le_sq
  rw [B0592.eLpNorm_two_sq, Cyl.cellμ, ← cell_eq_cylCell]
  exact B0592.lintegral_cell_sq_le hm c f

theorem integrable_cell_of_Xmc {c m : ℝ} (hm : 1 < m) (f : Xmc c m) :
    Integrable (f : Plane → ℝ) (volume.restrict (B0579.cell c)) :=
  ⟨(Lp.stronglyMeasurable f).aestronglyMeasurable,
    (B0592.lintegral_cell_le c f).trans_lt
      (ENNReal.mul_lt_top (B0592.weightConst_lt_top hm) ENNReal.ofReal_lt_top)⟩

/-- Near Biot–Savart velocity at radius `r`: `∫_{cell c} f(y) kNearR(x - y) dy`. -/
def uNearR (c r : ℝ) (f : Plane → ℝ) (x : Plane) : Cyl.Vec2 :=
  ∫ y in B0579.cell c, f y • kNearR c r (x - y)

/-- Far Biot–Savart velocity at radius `r`: `∫_{cell c} f(y) kFarR(x - y) dy`. -/
def uFarR (c r : ℝ) (f : Plane → ℝ) (x : Plane) : Cyl.Vec2 :=
  ∫ y in B0579.cell c, f y • kFarR c r (x - y)

theorem uNearR_eq_conv_extPer {c r : ℝ} (hc : 0 < c) (f : Plane → ℝ) (x : Plane) :
    uNearR c r f x = ∫ y in Cyl.cell c, extPer c f (x - y) • kNearR c r y := by
  have h1 : uNearR c r f x = ∫ y in Cyl.cell c, extPer c f y • kNearR c r (x - y) := by
    rw [uNearR, ← cell_eq_cylCell]
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y hy => ?_
    rw [extPer_of_mem_cell hc f hy]
  have hG : Cyl.IsPeriodic c (fun w => extPer c f (x - w) • kNearR c r w) := by
    intro w
    show extPer c f (x - (w.1 + c, w.2)) • kNearR c r (w.1 + c, w.2) =
      extPer c f (x - w) • kNearR c r w
    rw [isPeriodic_kNearR hc r w]
    congr 1
    have hsub := (isPeriodic_extPer hc f).sub_eq (x - w)
    rw [← hsub]
    congr 1
    ext <;> simp; ring
  have h2 := Cyl.integral_cell_comp_sub_left hc hG x
  rw [h1]
  simpa using h2

theorem stronglyMeasurable_uNearR (c r : ℝ) {f : Plane → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (uNearR c r f) := by
  have hF : StronglyMeasurable (Function.uncurry fun x y : Plane => f y • kNearR c r (x - y)) :=
    (hf.comp_measurable measurable_snd).smul
      ((measurable_kNearR c r).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact hF.integral_prod_right

theorem eLpNorm_uNearR_le {c r m : ℝ} (hc : 1 ≤ c) (hm : 0 ≤ m) (f : Xmc c m) :
    eLpNorm (uNearR c r f) 2 (Cyl.cellμ c) ≤
      (∫⁻ y in B0579.cell c, ‖kNearR c r y‖ₑ) * ENNReal.ofReal ‖f‖ := by
  have hc0 : 0 < c := by linarith
  have heq : uNearR c r f = fun x => ∫ y in Cyl.cell c, extPer c f (x - y) • kNearR c r y :=
    funext (uNearR_eq_conv_extPer hc0 f)
  rw [heq]
  have h1 := Cyl.eLpNorm_conv_periodic_le_vec hc0 (ν := volume.restrict (Cyl.cell c))
    (measurable_kNearR c r).stronglyMeasurable
    (stronglyMeasurable_extPer c (Lp.stronglyMeasurable f))
    (isPeriodic_extPer hc0 f) (p := 2) (by norm_num) (by norm_num)
  rw [eLpNorm_extPer_cellμ hc0] at h1
  refine h1.trans ?_
  rw [cell_eq_cylCell]
  gcongr
  exact eLpNorm_cell_le_norm hm f

theorem ae_integrable_kNearR {c r m : ℝ} (hc : 1 ≤ c) (hr : r ≤ 1) (hm : 1 < m) (f : Xmc c m) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Integrable (fun y => f y • kNearR c r (x - y)) (volume.restrict (B0579.cell c)) := by
  have hc0 : 0 < c := by linarith
  have hf_meas : Measurable (f : Plane → ℝ) := (Lp.stronglyMeasurable f).measurable
  have h_pt : ∀ x : Plane,
      ∫⁻ y in B0579.cell c, ‖f y • kNearR c r (x - y)‖ₑ =
        ∫⁻ y in Cyl.cell c, ‖extPer c f (x - y)‖ₑ * ‖kNearR c r y‖ₑ := by
    intro x
    have h1 : ∫⁻ y in B0579.cell c, ‖f y • kNearR c r (x - y)‖ₑ =
        ∫⁻ y in Cyl.cell c, ‖extPer c f y • kNearR c r (x - y)‖ₑ := by
      rw [← cell_eq_cylCell]
      refine setLIntegral_congr_fun (B0579.measurableSet_cell c) fun y hy => ?_
      rw [extPer_of_mem_cell hc0 f hy]
    have hG : Cyl.IsPeriodic c (fun w => ‖extPer c f (x - w) • kNearR c r w‖ₑ) := by
      intro w
      show ‖extPer c f (x - (w.1 + c, w.2)) • kNearR c r (w.1 + c, w.2)‖ₑ =
        ‖extPer c f (x - w) • kNearR c r w‖ₑ
      rw [isPeriodic_kNearR hc0 r w]
      have hsub := (isPeriodic_extPer hc0 f).sub_eq (x - w)
      have heq : (x - (w.1 + c, w.2) : Plane) = ((x - w).1 - c, (x - w).2) := by
        ext <;> simp; ring
      rw [heq, hsub]
    have h2 := Cyl.lintegral_cell_comp_sub_left hc0 hG x
    rw [h1]
    refine (by simpa using h2 :
      ∫⁻ y in Cyl.cell c, ‖extPer c f y • kNearR c r (x - y)‖ₑ =
        ∫⁻ y in Cyl.cell c, ‖extPer c f (x - y) • kNearR c r y‖ₑ).trans ?_
    refine lintegral_congr fun y => ?_
    rw [enorm_smul]
  have h_meas_inner : Measurable fun x : Plane =>
      ∫⁻ y in B0579.cell c, ‖f y • kNearR c r (x - y)‖ₑ := by
    have hF : Measurable fun p : Plane × Plane => ‖f p.2 • kNearR c r (p.1 - p.2)‖ₑ :=
      ((hf_meas.comp measurable_snd).smul
        ((measurable_kNearR c r).comp (measurable_fst.sub measurable_snd))).enorm
    exact hF.lintegral_prod_right'
  have h_tot : ∫⁻ x in B0579.cell c, ∫⁻ y in B0579.cell c, ‖f y • kNearR c r (x - y)‖ₑ < ∞ := by
    simp_rw [h_pt]
    rw [cell_eq_cylCell]
    have hm1 : Measurable (extPer c f) := hf_meas.comp (measurable_wrapPlane c)
    have hF2 : AEMeasurable (Function.uncurry fun x y : Plane =>
        ‖extPer c f (x - y)‖ₑ * ‖kNearR c r y‖ₑ)
        ((volume.restrict (Cyl.cell c)).prod (volume.restrict (Cyl.cell c))) :=
      (((hm1.comp (measurable_fst.sub measurable_snd)).enorm).mul
        ((measurable_kNearR c r).comp measurable_snd).enorm).aemeasurable
    rw [lintegral_lintegral_swap hF2]
    have h_shift : ∀ y : Plane,
        ∫⁻ x in Cyl.cell c, ‖extPer c f (x - y)‖ₑ * ‖kNearR c r y‖ₑ =
          (∫⁻ x in B0579.cell c, ‖f x‖ₑ) * ‖kNearR c r y‖ₑ := by
      intro y
      have hmx : Measurable fun x : Plane => ‖extPer c f (x - y)‖ₑ :=
        (hm1.comp (measurable_id.sub_const y)).enorm
      rw [lintegral_mul_const _ hmx]
      congr 1
      have hper : Cyl.IsPeriodic c (fun z => ‖extPer c f z‖ₑ) := fun z => by
        simp only [isPeriodic_extPer hc0 f z]
      have htr := Cyl.lintegral_cell_comp_add hc0 hper (-y)
      simp_rw [sub_eq_add_neg]
      rw [htr, ← cell_eq_cylCell]
      refine setLIntegral_congr_fun (B0579.measurableSet_cell c) fun x hx => ?_
      rw [extPer_of_mem_cell hc0 f hx]
    simp_rw [h_shift]
    rw [lintegral_const_mul _ (measurable_kNearR c r).enorm, ← cell_eq_cylCell]
    exact ENNReal.mul_lt_top (integrable_cell_of_Xmc hm f).2
      ((lintegral_kNearR_le hc hr).trans_lt ENNReal.ofReal_lt_top)
  filter_upwards [ae_lt_top h_meas_inner h_tot.ne] with x hx
  refine ⟨((Lp.stronglyMeasurable f).smul
    ((measurable_kNearR c r).comp (measurable_const.sub measurable_id)).stronglyMeasurable).aestronglyMeasurable,
    hx⟩

theorem integrable_kFarR {c r m : ℝ} (hc : 1 ≤ c) (hr : 0 < r) (hm : 1 < m) (f : Xmc c m)
    (x : Plane) :
    Integrable (fun y => f y • kFarR c r (x - y)) (volume.restrict (B0579.cell c)) := by
  have hf := integrable_cell_of_Xmc hm f
  refine Integrable.mono' (hf.norm.mul_const (r⁻¹ + 1)) ?_ (Eventually.of_forall fun y => ?_)
  · exact ((Lp.stronglyMeasurable f).smul
      ((measurable_kFarR c r).comp (measurable_const.sub measurable_id)).stronglyMeasurable).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_kFarR_le hc hr (x - y)) (norm_nonneg _)

theorem ae_integrable_bsKernel {c m : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (f : Xmc c m) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Integrable (fun y => f y • Cyl.bsKernel c (x - y)) (volume.restrict (B0579.cell c)) := by
  filter_upwards [ae_integrable_kNearR hc le_rfl hm f] with x hx
  have hfar := integrable_kFarR hc zero_lt_one hm f x
  refine (hx.add hfar).congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, ← smul_add, kNearR_add_kFarR]

theorem ae_K_eq_uNearR_add_uFarR {c r m : ℝ} (hc : 1 ≤ c) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hm : 1 < m) (f : Xmc c m) :
    ∀ᵐ x ∂(B0579.cellMeasure c m), Cyl.K c f x = uNearR c r f x + uFarR c r f x := by
  filter_upwards [(B0579.cellMeasure_ac c m).ae_le (ae_integrable_kNearR hc hr1 hm f)] with x hx
  have hfar := integrable_kFarR hc hr0 hm f x
  rw [Cyl.K, ← cell_eq_cylCell, uNearR, uFarR, ← integral_add hx hfar]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [← smul_add, kNearR_add_kFarR]

/-! ## 4. Near weighted interaction estimate on `Xmc c m` -/

/-- Near part of `cylWeightedOpFun`: `-(uNearR c r f x · b x)`. -/
def nearOpFun (c r : ℝ) (b : Plane → Plane) (f : Plane → ℝ) (x : Plane) : ℝ :=
  -(uNearR c r f x 0 * (b x).1 + uNearR c r f x 1 * (b x).2)

/-- Far part of `cylWeightedOpFun`: `-(uFarR c r f x · b x)`. -/
def farOpFun (c r : ℝ) (b : Plane → Plane) (f : Plane → ℝ) (x : Plane) : ℝ :=
  -(uFarR c r f x 0 * (b x).1 + uFarR c r f x 1 * (b x).2)

theorem ae_cylWeightedOpFun_eq_near_add_far {c r m : ℝ} (hc : 1 ≤ c) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hm : 1 < m) (b : Plane → Plane) (f : Xmc c m) :
    cylWeightedOpFun c b f =ᵐ[B0579.cellMeasure c m]
      fun x => nearOpFun c r b f x + farOpFun c r b f x := by
  filter_upwards [ae_K_eq_uNearR_add_uFarR hc hr0 hr1 hm f] with x hx
  simp only [cylWeightedOpFun, nearOpFun, farOpFun, hx, PiLp.add_apply]
  ring

theorem norm_jb_mul_nearOpFun_le {c r m B : ℝ} {b : Plane → Plane}
    (hb : IsCylWeightedCoeff c m B b) (f : Plane → ℝ) {x : Plane} (hx : x ∈ B0579.cell c) :
    ‖B0579.jb x ^ (m / 2) * nearOpFun c r b f x‖ ≤ B * ‖uNearR c r f x‖ := by
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hpow : B0579.jb x ^ (m / 2) ≤ B0579.jb x ^ (m / 2 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hjb1 (by linarith)
  have h0 : |uNearR c r f x 0| ≤ ‖uNearR c r f x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (uNearR c r f x) 0
  have h1 : |uNearR c r f x 1| ≤ ‖uNearR c r f x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (uNearR c r f x) 1
  have hnear : |nearOpFun c r b f x| ≤ (|(b x).1| + |(b x).2|) * ‖uNearR c r f x‖ := by
    unfold nearOpFun
    rw [abs_neg]
    calc |uNearR c r f x 0 * (b x).1 + uNearR c r f x 1 * (b x).2|
        ≤ |uNearR c r f x 0 * (b x).1| + |uNearR c r f x 1 * (b x).2| := abs_add_le _ _
      _ = |uNearR c r f x 0| * |(b x).1| + |uNearR c r f x 1| * |(b x).2| := by
          rw [abs_mul, abs_mul]
      _ ≤ ‖uNearR c r f x‖ * |(b x).1| + ‖uNearR c r f x‖ * |(b x).2| := by gcongr
      _ = (|(b x).1| + |(b x).2|) * ‖uNearR c r f x‖ := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
  calc B0579.jb x ^ (m / 2) * |nearOpFun c r b f x|
      ≤ B0579.jb x ^ (m / 2 + 1) * ((|(b x).1| + |(b x).2|) * ‖uNearR c r f x‖) :=
        mul_le_mul hpow hnear (abs_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le _)
    _ = ((|(b x).1| + |(b x).2|) * B0579.jb x ^ (m / 2 + 1)) * ‖uNearR c r f x‖ := by ring
    _ ≤ B * ‖uNearR c r f x‖ :=
        mul_le_mul_of_nonneg_right (hb.2 x hx) (norm_nonneg _)

theorem nearOpFun_memLp_and_bound {c r m B : ℝ} (hc : 1 ≤ c) (hr : r ≤ 1) (hm : 0 ≤ m)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (f : Xmc c m) :
    MemLp (nearOpFun c r b f) 2 (B0579.cellMeasure c m) ∧
      eLpNorm (nearOpFun c r b f) 2 (B0579.cellMeasure c m) ≤
        ENNReal.ofReal B * ((∫⁻ y in B0579.cell c, ‖kNearR c r y‖ₑ) * ENNReal.ofReal ‖f‖) := by
  have hu : StronglyMeasurable (uNearR c r f) :=
    stronglyMeasurable_uNearR c r (Lp.stronglyMeasurable f)
  have hnear_meas : Measurable (nearOpFun c r b f) := by
    unfold nearOpFun
    refine Measurable.neg (Measurable.add ?_ ?_)
    · exact ((EuclideanSpace.proj 0 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp hu.measurable).mul
        (continuous_fst.comp hb.1).measurable
    · exact ((EuclideanSpace.proj 1 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp hu.measurable).mul
        (continuous_snd.comp hb.1).measurable
  have hbd : eLpNorm (nearOpFun c r b f) 2 (B0579.cellMeasure c m) ≤
      ENNReal.ofReal B * ((∫⁻ y in B0579.cell c, ‖kNearR c r y‖ₑ) * ENNReal.ofReal ‖f‖) := by
    rw [B0579.eLpNorm_cellMeasure]
    have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (μ := volume.restrict (B0579.cell c)) (p := 2)
      (f := fun x => B0579.jb x ^ (m / 2) * nearOpFun c r b f x)
      (g := uNearR c r f) (c := B)
      (ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun x hx =>
        norm_jb_mul_nearOpFun_le hb f hx)
    have heq : eLpNorm (uNearR c r f) 2 (volume.restrict (B0579.cell c)) =
        eLpNorm (uNearR c r f) 2 (Cyl.cellμ c) := by
      rw [cell_eq_cylCell, Cyl.cellμ]
    rw [heq] at h1
    exact h1.trans (by gcongr; exact eLpNorm_uNearR_le hc hm f)
  refine ⟨⟨hnear_meas.aestronglyMeasurable, hbd.trans_lt ?_⟩, hbd⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ((lintegral_kNearR_le hc hr).trans_lt ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top)

/-! ## 5. Far Hilbert–Schmidt operator on `Xmc c m` -/

instance instSFiniteCellMeasure (c m : ℝ) : SFinite (B0579.cellMeasure c m) := by
  unfold B0579.cellMeasure
  infer_instance

/-- The Hilbert–Schmidt kernel of `farOpFun c r b` on `Xmc c m`:
`-(kFarR(x - y) · b(x)) jb(y)^{-m}`. -/
def hsCylKernel (c m r : ℝ) (b : Plane → Plane) (z : Plane × Plane) : ℝ :=
  -(kFarR c r (z.1 - z.2) 0 * (b z.1).1 + kFarR c r (z.1 - z.2) 1 * (b z.1).2) *
    B0579.jb z.2 ^ (-m)

theorem integral_hsCylKernel {c m r : ℝ} (hc : 1 ≤ c) (hr : 0 < r) (hm : 1 < m)
    (b : Plane → Plane) (f : Xmc c m) (x : Plane) :
    ∫ y, hsCylKernel c m r b (x, y) * f y ∂(B0579.cellMeasure c m) = farOpFun c r b f x := by
  rw [B0579.integral_cellMeasure]
  have hfar := integrable_kFarR hc hr hm f x
  have hi : ∀ i : Fin 2,
      Integrable (fun y => f y * kFarR c r (x - y) i) (volume.restrict (B0579.cell c)) := fun i => by
    have hcomp := (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hfar
    exact hcomp.congr (Eventually.of_forall fun y => by simp)
  have hint_eq : ∀ i : Fin 2,
      ∫ y in B0579.cell c, f y * kFarR c r (x - y) i = uFarR c r f x i := fun i => by
    have hcomp := (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hfar
    simpa [uFarR] using hcomp
  have hcongr : ∀ y : Plane,
      B0579.density m y • (hsCylKernel c m r b (x, y) * f y) =
        -((f y * kFarR c r (x - y) 0) * (b x).1 + (f y * kFarR c r (x - y) 1) * (b x).2) := by
    intro y
    rw [NNReal.smul_def, smul_eq_mul, B0579.coe_density]
    unfold hsCylKernel
    have hjb : B0579.jb y ^ m * B0579.jb y ^ (-m) = 1 := by
      rw [B0579.jb_rpow_mul, add_neg_cancel, Real.rpow_zero]
    calc B0579.jb y ^ m * (-(kFarR c r (x - y) 0 * (b x).1 + kFarR c r (x - y) 1 * (b x).2) *
            B0579.jb y ^ (-m) * f y)
        = (B0579.jb y ^ m * B0579.jb y ^ (-m)) *
            (-((f y * kFarR c r (x - y) 0) * (b x).1 + (f y * kFarR c r (x - y) 1) * (b x).2)) := by
          ring
      _ = -((f y * kFarR c r (x - y) 0) * (b x).1 + (f y * kFarR c r (x - y) 1) * (b x).2) := by
          rw [hjb, one_mul]
  simp_rw [hcongr]
  rw [integral_neg, integral_add ((hi 0).mul_const _) ((hi 1).mul_const _),
    integral_mul_const, integral_mul_const, hint_eq 0, hint_eq 1, farOpFun]

private theorem eLpNorm_jb_neg_half_add_one (c m : ℝ) :
    eLpNorm (fun x : Plane => B0579.jb x ^ (-(m / 2 + 1))) 2 (B0579.cellMeasure c m) ≤
      B0592.weightConst 2 := by
  apply B0592.ennreal_le_of_sq_le_sq
  rw [B0579.eLpNorm_cellMeasure, B0592.eLpNorm_two_sq, B0592.weightConst,
    B0592.ennreal_rpow_half_sq]
  refine (setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_congr fun x => ?_))
  have h1 : B0579.jb x ^ (m / 2) * B0579.jb x ^ (-(m / 2 + 1)) = B0579.jb x ^ (-1 : ℝ) := by
    rw [B0579.jb_rpow_mul]
    congr 1
    ring
  rw [h1, Real.enorm_eq_ofReal (Real.rpow_nonneg (B0579.jb_pos x).le _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos x).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  congr 2
  push_cast
  ring

private theorem eLpNorm_jb_neg_m (c m : ℝ) :
    eLpNorm (fun y : Plane => B0579.jb y ^ (-m)) 2 (B0579.cellMeasure c m) ≤
      B0592.weightConst m := by
  apply B0592.ennreal_le_of_sq_le_sq
  rw [B0579.eLpNorm_cellMeasure, B0592.eLpNorm_two_sq, B0592.weightConst,
    B0592.ennreal_rpow_half_sq]
  refine (setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_congr fun y => ?_))
  have h1 : B0579.jb y ^ (m / 2) * B0579.jb y ^ (-m) = B0579.jb y ^ (-m / 2) := by
    rw [B0579.jb_rpow_mul]
    congr 1
    ring
  rw [h1, Real.enorm_eq_ofReal (Real.rpow_nonneg (B0579.jb_pos y).le _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos y).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos y).le]
  congr 2
  push_cast
  ring

theorem memLp_hsCylKernel_and_bound {c m r B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hr : 0 < r)
    (_hB : 0 ≤ B) {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) :
    MemLp (hsCylKernel c m r b) 2 ((B0579.cellMeasure c m).prod (B0579.cellMeasure c m)) ∧
      eLpNorm (hsCylKernel c m r b) 2 ((B0579.cellMeasure c m).prod (B0579.cellMeasure c m)) ≤
        ENNReal.ofReal ((r⁻¹ + 1) * B) * (B0592.weightConst 2 * B0592.weightConst m) := by
  set μ := B0579.cellMeasure c m
  set u : Plane → ℝ := fun x => B0579.jb x ^ (-(m / 2 + 1))
  set v : Plane → ℝ := fun y => B0579.jb y ^ (-m)
  have hu_meas : Measurable u := (B0579.continuous_jb_rpow _).measurable
  have hv_meas : Measurable v := (B0579.continuous_jb_rpow _).measurable
  have hk_meas : Measurable (hsCylKernel c m r b) := by
    unfold hsCylKernel
    refine (Measurable.neg (Measurable.add ?_ ?_)).mul (hv_meas.comp measurable_snd)
    · exact ((EuclideanSpace.proj 0 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp
        ((measurable_kFarR c r).comp (measurable_fst.sub measurable_snd))).mul
        (continuous_fst.comp (hb.1.comp continuous_fst)).measurable
    · exact ((EuclideanSpace.proj 1 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp
        ((measurable_kFarR c r).comp (measurable_fst.sub measurable_snd))).mul
        (continuous_snd.comp (hb.1.comp continuous_fst)).measurable
  have hprod_bound : eLpNorm (fun z : Plane × Plane => u z.1 * v z.2) 2 (μ.prod μ) ≤
      B0592.weightConst 2 * B0592.weightConst m := by
    apply B0592.ennreal_le_of_sq_le_sq
    rw [B0592.eLpNorm_two_sq]
    have hF : AEMeasurable (fun z : Plane × Plane => ‖u z.1 * v z.2‖ₑ ^ 2) (μ.prod μ) :=
      (((hu_meas.comp measurable_fst).mul (hv_meas.comp measurable_snd)).enorm.pow_const 2).aemeasurable
    rw [lintegral_prod _ hF]
    have hsplit : ∀ x : Plane,
        ∫⁻ y, ‖u x * v y‖ₑ ^ 2 ∂μ = ‖u x‖ₑ ^ 2 * ∫⁻ y, ‖v y‖ₑ ^ 2 ∂μ := by
      intro x
      have hcongr : ∀ y : Plane, ‖u x * v y‖ₑ ^ 2 = ‖u x‖ₑ ^ 2 * ‖v y‖ₑ ^ 2 := fun y => by
        rw [enorm_mul, mul_pow]
      simp_rw [hcongr]
      exact lintegral_const_mul _ (hv_meas.enorm.pow_const 2)
    simp_rw [hsplit]
    rw [lintegral_mul_const _ (hu_meas.enorm.pow_const 2), ← B0592.eLpNorm_two_sq,
      ← B0592.eLpNorm_two_sq]
    have hu2 : eLpNorm u 2 μ ^ 2 ≤ B0592.weightConst 2 ^ 2 :=
      pow_le_pow_left₀ zero_le (eLpNorm_jb_neg_half_add_one c m) 2
    have hv2 : eLpNorm v 2 μ ^ 2 ≤ B0592.weightConst m ^ 2 :=
      pow_le_pow_left₀ zero_le (eLpNorm_jb_neg_m c m) 2
    calc eLpNorm u 2 μ ^ 2 * eLpNorm v 2 μ ^ 2
        ≤ B0592.weightConst 2 ^ 2 * B0592.weightConst m ^ 2 := mul_le_mul' hu2 hv2
      _ = (B0592.weightConst 2 * B0592.weightConst m) ^ 2 := by ring
  have hae_cell : ∀ᵐ z : Plane × Plane ∂(μ.prod μ), z.1 ∈ B0579.cell c := by
    have hx : ∀ᵐ x ∂μ, x ∈ B0579.cell c :=
      (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hx
  have hpt : ∀ᵐ z : Plane × Plane ∂(μ.prod μ),
      ‖hsCylKernel c m r b z‖ ≤ ((r⁻¹ + 1) * B) * ‖u z.1 * v z.2‖ := by
    filter_upwards [hae_cell] with z hz
    have h0 := norm_kFarR_coord_le hc hr (z.1 - z.2) 0
    have h1 := norm_kFarR_coord_le hc hr (z.1 - z.2) 1
    have hfar_dot :
        |kFarR c r (z.1 - z.2) 0 * (b z.1).1 + kFarR c r (z.1 - z.2) 1 * (b z.1).2| ≤
          (r⁻¹ + 1) * (|(b z.1).1| + |(b z.1).2|) := by
      calc |kFarR c r (z.1 - z.2) 0 * (b z.1).1 + kFarR c r (z.1 - z.2) 1 * (b z.1).2|
          ≤ |kFarR c r (z.1 - z.2) 0| * |(b z.1).1| + |kFarR c r (z.1 - z.2) 1| * |(b z.1).2| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ (r⁻¹ + 1) * |(b z.1).1| + (r⁻¹ + 1) * |(b z.1).2| := by gcongr
        _ = (r⁻¹ + 1) * (|(b z.1).1| + |(b z.1).2|) := by ring
    have hb_le : |(b z.1).1| + |(b z.1).2| ≤ B * u z.1 := by
      have hmul := hb.2 z.1 hz
      have hpos : 0 < B0579.jb z.1 ^ (m / 2 + 1) := Real.rpow_pos_of_pos (B0579.jb_pos z.1) _
      have hinv : B0579.jb z.1 ^ (m / 2 + 1) * u z.1 = 1 := by
        simp only [u]
        rw [B0579.jb_rpow_mul, add_neg_cancel, Real.rpow_zero]
      calc |(b z.1).1| + |(b z.1).2|
          = (|(b z.1).1| + |(b z.1).2|) * (B0579.jb z.1 ^ (m / 2 + 1) * u z.1) := by
            rw [hinv, mul_one]
        _ = ((|(b z.1).1| + |(b z.1).2|) * B0579.jb z.1 ^ (m / 2 + 1)) * u z.1 := by ring
        _ ≤ B * u z.1 := mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg (B0579.jb_pos z.1).le _)
    have hu_nn : 0 ≤ u z.1 := Real.rpow_nonneg (B0579.jb_pos z.1).le _
    have hv_nn : 0 ≤ v z.2 := Real.rpow_nonneg (B0579.jb_pos z.2).le _
    simp only [hsCylKernel, Real.norm_eq_abs]
    rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hu_nn, abs_of_nonneg hv_nn]
    calc |kFarR c r (z.1 - z.2) 0 * (b z.1).1 + kFarR c r (z.1 - z.2) 1 * (b z.1).2| * v z.2
        ≤ ((r⁻¹ + 1) * (|(b z.1).1| + |(b z.1).2|)) * v z.2 :=
          mul_le_mul_of_nonneg_right hfar_dot hv_nn
      _ ≤ ((r⁻¹ + 1) * (B * u z.1)) * v z.2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb_le (by positivity)) hv_nn
      _ = ((r⁻¹ + 1) * B) * (u z.1 * v z.2) := by ring
  have hbd : eLpNorm (hsCylKernel c m r b) 2 (μ.prod μ) ≤
      ENNReal.ofReal ((r⁻¹ + 1) * B) * (B0592.weightConst 2 * B0592.weightConst m) := by
    have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ.prod μ) (p := 2)
      (f := hsCylKernel c m r b) (g := fun z : Plane × Plane => u z.1 * v z.2)
      (c := (r⁻¹ + 1) * B) hpt
    exact h1.trans (by gcongr)
  refine ⟨⟨hk_meas.aestronglyMeasurable, hbd.trans_lt ?_⟩, hbd⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (B0592.weightConst_lt_top (by norm_num)) (B0592.weightConst_lt_top hm))

instance sigmaFinite_cellMeasure (c m : ℝ) : SigmaFinite (B0579.cellMeasure c m) := by
  rw [B0579.cellMeasure]
  infer_instance

/-- The far Hilbert–Schmidt operator at truncation index `n` (`r = B0061.rad n`). -/
def hsCylOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B) {b : Plane → Plane}
    (hb : IsCylWeightedCoeff c m B b) (n : ℕ) : Xmc c m →L[ℝ] Xmc c m :=
  realKernelOperator (memLp_hsCylKernel_and_bound hc hm (B0061.rad_pos n) hB hb).1

theorem isCompactOperator_hsCylOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (n : ℕ) :
    IsCompactOperator (hsCylOp hc hm hB hb n) :=
  isCompactOperator_realKernelOperator _

theorem coeFn_hsCylOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (n : ℕ) (f : Xmc c m) :
    (hsCylOp hc hm hB hb n f : Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
      farOpFun c (B0061.rad n) b f := by
  filter_upwards [coeFn_realKernelOperator
    (memLp_hsCylKernel_and_bound hc hm (B0061.rad_pos n) hB hb).1 f] with x hx
  rw [hsCylOp, hx, integral_hsCylKernel hc (B0061.rad_pos n) hm b f x]

theorem norm_hsCylOp_zero_le {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) :
    ‖hsCylOp hc hm hB hb 0‖ ≤
      2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B := by
  have h1 := norm_realKernelOperator_le
    (memLp_hsCylKernel_and_bound hc hm (B0061.rad_pos 0) hB hb).1
  have h2 := (memLp_hsCylKernel_and_bound hc hm (B0061.rad_pos 0) hB hb).2
  have hrad0 : (B0061.rad 0)⁻¹ + 1 = 2 := by
    unfold B0061.rad
    norm_num
  rw [hrad0] at h2
  have hfin : ENNReal.ofReal (2 * B) * (B0592.weightConst 2 * B0592.weightConst m) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (B0592.weightConst_lt_top (by norm_num)).ne
        (B0592.weightConst_lt_top hm).ne)
  have h3 := ENNReal.toReal_mono hfin h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h3
  calc ‖hsCylOp hc hm hB hb 0‖
      ≤ 2 * B * ((B0592.weightConst 2).toReal * (B0592.weightConst m).toReal) :=
        h1.trans h3
    _ = 2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B := by ring

/-! ## 6. Construction, operator-norm bound, and compactness of `cylWeightedOp` -/

theorem ae_cylWeightedOpFun_eq_near_add_hsCylOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m)
    (hB : 0 ≤ B) {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (n : ℕ) (f : Xmc c m) :
    cylWeightedOpFun c b f =ᵐ[B0579.cellMeasure c m]
      nearOpFun c (B0061.rad n) b f + (hsCylOp hc hm hB hb n f : Plane → ℝ) := by
  filter_upwards [ae_cylWeightedOpFun_eq_near_add_far hc (B0061.rad_pos n) (B0061.rad_le_one n)
    hm b f, coeFn_hsCylOp hc hm hB hb n f] with x hx1 hx2
  rw [Pi.add_apply, hx2, hx1]

theorem memLp_cylWeightedOpFun {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (f : Xmc c m) :
    MemLp (cylWeightedOpFun c b f) 2 (B0579.cellMeasure c m) := by
  have hnear := (nearOpFun_memLp_and_bound hc (B0061.rad_le_one 0) (by linarith) hb f).1
  exact (hnear.add (Lp.memLp (hsCylOp hc hm hB hb 0 f))).ae_eq
    (ae_cylWeightedOpFun_eq_near_add_hsCylOp hc hm hB hb 0 f).symm

/-- `f ↦ -(K_c f)·b` on `Xmc c m` as an `Lp` function. -/
def cylWeightedLpFun {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (f : Xmc c m) : Xmc c m :=
  (memLp_cylWeightedOpFun hc hm hB hb f).toLp _

theorem coeFn_cylWeightedLpFun {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (f : Xmc c m) :
    (cylWeightedLpFun hc hm hB hb f : Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
      cylWeightedOpFun c b f :=
  MemLp.coeFn_toLp _

theorem norm_cylWeightedLpFun_sub_hsCylOp_le {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (n : ℕ) (f : Xmc c m) :
    ‖cylWeightedLpFun hc hm hB hb f - hsCylOp hc hm hB hb n f‖ ≤
      B * (∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ).toReal * ‖f‖ := by
  have hnear := nearOpFun_memLp_and_bound hc (B0061.rad_le_one n) (by linarith) hb f
  have hae : ((cylWeightedLpFun hc hm hB hb f - hsCylOp hc hm hB hb n f : Xmc c m) : Plane → ℝ)
      =ᵐ[B0579.cellMeasure c m] nearOpFun c (B0061.rad n) b f := by
    filter_upwards [Lp.coeFn_sub (cylWeightedLpFun hc hm hB hb f) (hsCylOp hc hm hB hb n f),
      coeFn_cylWeightedLpFun hc hm hB hb f,
      ae_cylWeightedOpFun_eq_near_add_hsCylOp hc hm hB hb n f] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.add_apply, add_sub_cancel_right]
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have hfin : (∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ) ≠ ∞ :=
    ((lintegral_kNearR_le hc (B0061.rad_le_one n)).trans_lt ENNReal.ofReal_lt_top).ne
  have hprod_fin :
      ENNReal.ofReal B * ((∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ) *
        ENNReal.ofReal ‖f‖) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
  calc (eLpNorm (nearOpFun c (B0061.rad n) b f) 2 (B0579.cellMeasure c m)).toReal
      ≤ (ENNReal.ofReal B * ((∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ) *
          ENNReal.ofReal ‖f‖)).toReal :=
        ENNReal.toReal_mono hprod_fin hnear.2
    _ = B * (∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ).toReal * ‖f‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
          ENNReal.toReal_ofReal (norm_nonneg _)]
        ring

theorem cylWeightedLpFun_add {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (f g : Xmc c m) :
    cylWeightedLpFun hc hm hB hb (f + g) =
      cylWeightedLpFun hc hm hB hb f + cylWeightedLpFun hc hm hB hb g := by
  apply Lp.ext
  have hfg_ae : ((f + g : Xmc c m) : Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] f + g :=
    (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_add f g)
  have hK_add : ∀ᵐ x ∂(B0579.cellMeasure c m),
      Cyl.K c (f + g : Xmc c m) x = Cyl.K c f x + Cyl.K c g x := by
    filter_upwards [(B0579.cellMeasure_ac c m).ae_le (ae_integrable_bsKernel hc hm f),
      (B0579.cellMeasure_ac c m).ae_le (ae_integrable_bsKernel hc hm g)] with x hif hig
    rw [Cyl.K, Cyl.K, Cyl.K, ← cell_eq_cylCell, ← integral_add hif hig]
    refine integral_congr_ae ?_
    filter_upwards [hfg_ae] with y hy
    rw [hy, Pi.add_apply, add_smul]
  filter_upwards [coeFn_cylWeightedLpFun hc hm hB hb (f + g),
    Lp.coeFn_add (cylWeightedLpFun hc hm hB hb f) (cylWeightedLpFun hc hm hB hb g),
    coeFn_cylWeightedLpFun hc hm hB hb f,
    coeFn_cylWeightedLpFun hc hm hB hb g,
    hK_add] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4]
  simp only [cylWeightedOpFun, h5, PiLp.add_apply]
  ring

theorem cylWeightedLpFun_smul {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (a : ℝ) (f : Xmc c m) :
    cylWeightedLpFun hc hm hB hb (a • f) = a • cylWeightedLpFun hc hm hB hb f := by
  apply Lp.ext
  have haf_ae : ((a • f : Xmc c m) : Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] a • f :=
    (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_smul a f)
  have hK_smul : ∀ x : Plane, Cyl.K c (a • f : Xmc c m) x = a • Cyl.K c f x := by
    intro x
    rw [Cyl.K, Cyl.K, ← cell_eq_cylCell, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [haf_ae] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_smul]
  filter_upwards [coeFn_cylWeightedLpFun hc hm hB hb (a • f),
    Lp.coeFn_smul a (cylWeightedLpFun hc hm hB hb f),
    coeFn_cylWeightedLpFun hc hm hB hb f] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  simp only [cylWeightedOpFun, hK_smul x, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The constant `C_K(m) = max 1 (2 C_2 C_m + nearKernelConst) > 0` in `CylWeightedKernelStep`. -/
def cylKernelBoundConst (m : ℝ) : ℝ :=
  max 1 (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal + nearKernelConst)

theorem cylKernelBoundConst_pos (m : ℝ) : 0 < cylKernelBoundConst m :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem norm_cylWeightedLpFun_le {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) (f : Xmc c m) :
    ‖cylWeightedLpFun hc hm hB hb f‖ ≤ cylKernelBoundConst m * B * ‖f‖ := by
  have hsub := norm_cylWeightedLpFun_sub_hsCylOp_le hc hm hB hb 0 f
  have hnear0 : (∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad 0) y‖ₑ).toReal ≤ nearKernelConst := by
    have h1 := lintegral_kNearR_le hc (B0061.rad_le_one 0)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans
      (le_of_eq (ENNReal.toReal_ofReal nearKernelConst_nonneg))
  have hhs0 : ‖hsCylOp hc hm hB hb 0 f‖ ≤
      (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B) * ‖f‖ :=
    ((hsCylOp hc hm hB hb 0).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (norm_hsCylOp_zero_le hc hm hB hb) (norm_nonneg f))
  have hsub0 : ‖cylWeightedLpFun hc hm hB hb f - hsCylOp hc hm hB hb 0 f‖ ≤
      (B * nearKernelConst) * ‖f‖ :=
    hsub.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnear0 hB) (norm_nonneg f))
  have hle_max :
      2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal + nearKernelConst ≤
        cylKernelBoundConst m :=
    le_max_right _ _
  calc ‖cylWeightedLpFun hc hm hB hb f‖
      ≤ ‖hsCylOp hc hm hB hb 0 f‖ +
          ‖cylWeightedLpFun hc hm hB hb f - hsCylOp hc hm hB hb 0 f‖ :=
        norm_le_insert' _ _
    _ ≤ (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B) * ‖f‖ +
          (B * nearKernelConst) * ‖f‖ :=
        add_le_add hhs0 hsub0
    _ = (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal + nearKernelConst) *
          B * ‖f‖ := by ring
    _ ≤ cylKernelBoundConst m * B * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_max hB) (norm_nonneg f)

/-- The bounded cylinder weighted Biot–Savart operator `f ↦ -(K_c f)·b` on `Xmc c m`. -/
def cylWeightedOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) : Xmc c m →L[ℝ] Xmc c m :=
  LinearMap.mkContinuous
    { toFun := cylWeightedLpFun hc hm hB hb
      map_add' := cylWeightedLpFun_add hc hm hB hb
      map_smul' := fun a f => by
        rw [RingHom.id_apply]
        exact cylWeightedLpFun_smul hc hm hB hb a f }
    (cylKernelBoundConst m * B)
    (norm_cylWeightedLpFun_le hc hm hB hb)

theorem isCylWeightedOp_cylWeightedOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) :
    IsCylWeightedOp c m b (cylWeightedOp hc hm hB hb) :=
  coeFn_cylWeightedLpFun hc hm hB hb

theorem norm_cylWeightedOp_le {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) :
    ‖cylWeightedOp hc hm hB hb‖ ≤ cylKernelBoundConst m * B :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (cylKernelBoundConst_pos m).le hB) _

theorem isCompactOperator_cylWeightedOp {c m B : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsCylWeightedCoeff c m B b) :
    IsCompactOperator (cylWeightedOp hc hm hB hb) := by
  have hL : Tendsto (fun n : ℕ =>
      B * (∫⁻ y in B0579.cell c, ‖kNearR c (B0061.rad n) y‖ₑ).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_lintegral_kNearR hc)
    simpa using h.const_mul B
  have hT : Tendsto (fun n : ℕ => hsCylOp hc hm hB hb n) atTop
      (𝓝 (cylWeightedOp hc hm hB hb)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hB ENNReal.toReal_nonneg) fun f => ?_
    rw [show (hsCylOp hc hm hB hb n - cylWeightedOp hc hm hB hb) f =
        hsCylOp hc hm hB hb n f - cylWeightedLpFun hc hm hB hb f from rfl, norm_sub_rev]
    exact norm_cylWeightedLpFun_sub_hsCylOp_le hc hm hB hb n f
  exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto hT
    (Eventually.of_forall fun n => isCompactOperator_hsCylOp hc hm hB hb n)

/-- **Main theorem (`PartII-b:F1/1`)**: cylinder weighted Biot–Savart operator bound and
compactness (`CylWeightedKernelStep`). -/
theorem cylWeightedKernelStep_proof : CylWeightedKernelStep := by
  intro m hm
  have hm1 : 1 < m := by linarith
  refine ⟨cylKernelBoundConst m, cylKernelBoundConst_pos m, ?_⟩
  intro c hc B hB b hb
  exact ⟨cylWeightedOp hc hm1 hB hb,
    isCylWeightedOp_cylWeightedOp hc hm1 hB hb,
    isCompactOperator_cylWeightedOp hc hm1 hB hb,
    norm_cylWeightedOp_le hc hm1 hB hb⟩

end UnforcedLeray.Short.IIb

namespace Short.PartIIb

abbrev CylWeightedKernelStep : Prop := UnforcedLeray.Short.IIb.CylWeightedKernelStep

theorem cylWeightedKernelStep_proof : CylWeightedKernelStep :=
  UnforcedLeray.Short.IIb.cylWeightedKernelStep_proof

end Short.PartIIb

end
