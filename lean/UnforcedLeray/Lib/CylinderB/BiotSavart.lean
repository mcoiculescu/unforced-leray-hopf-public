import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Lib.CylinderB.Leray
import UnforcedLeray.Lib.Kernels.CylinderBS
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.RingTheory.TotallySplit

/-!
# CY11 (part): the cylinder Biot–Savart operator `K_c ω` on the kernel of INF22 K8


(§5 Layer 2; decision D14: the kernel is defined once, in `Lib/Kernels/CylinderBS`
(`Kernels.cylinderBS c z = (2πi)⁻¹ (π/c) cot(πz/c)`), and the operator is built here).

Manuscript: `paper/main.tex` lines 13840–13866 (B0655: `K_c` is the periodized planar kernel on
`(ℝ/cℤ) × ℝ`), 13917–13925 (B0658: `K_c = k_near + k_far`, `|k_near| ≤ C/|x|` on `|x| < 1`,
`k_far` bounded, uniformly for `c ≥ 1`), 9594–9608 (B0592).

In complex notation `z = q + iη`, `u₁ − i u₂ = K_c ⋆ ω`, so the velocity kernel is
`(Re K_c, −Im K_c)` (for the planar kernel `(2πiz)⁻¹` this is `(−η, q)/(2π|z|²)`).

## Main declarations
* `bsC c z`, `bsKernel c z : Vec2`, `isPeriodic_bsKernel`, `norm_bsKernel`;
* `norm_bsKernel_le`: `‖K_c(z)‖ ≤ |z|⁻¹ + 1` on the centred cell, uniformly in `c ≥ 1`, with the
  Euclidean modulus `|z| = √(q² + η²)` (B0658, B0592; the near/far split of the kernel);
* `K c ω x = ∫_cell ω(y) K_c(x − y) dy`, `isPeriodic_K`, `K_eq_reflect`
  (`K c ω x = ∫_cell ω(x − y) K_c(y) dy`, the centred form of the near/far split);
* `kNear`, `kFar`, `bsKernel_split`: on the cell `K_c = k_near + k_far` with
  `∫_cell |k_near| ≤ C` and `|k_far| ≤ 2`, `C` independent of `c ≥ 1` (B0658);
* `uNear`, `uFar`, `K_split`: `K_c ω = u_near + u_far` (wherever both integrals converge), with
  `‖u_near‖_{L²(cell)} ≤ C ‖ω‖_{L²(cell)}` and `|u_far| ≤ 2 ‖ω‖_{L¹(cell)}` (B0658:
  `‖K_c f‖_{L²+L^∞} ≤ C(‖f‖₁ + ‖f‖₂)`).

Not built: `qMode_K`, `qAvg_K`,
`weak_curl_K`, `norm_grad_K_le`, `norm_K_H1_le`, `norm_K_L2_even_le`, `norm_K_top_le`,
`K_adjoint`, `K_scale`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex

namespace UnforcedLeray.Cyl

variable {c : ℝ}

/-- The complex cylinder kernel at `z = q + iη` (INF22 K8). -/
def bsC (c : ℝ) (z : Plane) : ℂ := Kernels.cylinderBS c ((z.1 : ℂ) + (z.2 : ℂ) * I)

/-- **The cylinder Biot–Savart kernel** as a meridional vector `(Re K_c, −Im K_c)`. -/
def bsKernel (c : ℝ) (z : Plane) : Vec2 := vec (bsC c z).re (-(bsC c z).im)

theorem isPeriodic_bsC (c : ℝ) : IsPeriodic c (bsC c) := by
  intro z
  simp only [bsC]
  have e : (((z.1 + c : ℝ) : ℂ) + (z.2 : ℂ) * I) = ((z.1 : ℂ) + (z.2 : ℂ) * I) + c := by
    push_cast; ring
  rw [e, Kernels.cylinderBS_periodic]

theorem isPeriodic_bsKernel (c : ℝ) : IsPeriodic c (bsKernel c) := fun z => by
  simp only [bsKernel, isPeriodic_bsC c z]

theorem norm_vec (a b : ℝ) : ‖vec a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_bsKernel (c : ℝ) (z : Plane) : ‖bsKernel c z‖ = ‖bsC c z‖ := by
  rw [bsKernel, norm_vec, neg_sq, Complex.norm_eq_sqrt_sq_add_sq]

/-- **The near/far bound of the kernel** (B0658 tex 13917–13925, B0592): on the centred cell
`|q| ≤ c/2`, uniformly in `c ≥ 1`, `‖K_c(z)‖ ≤ |z|⁻¹ + 1` with `|z| = √(q² + η²)`. -/
theorem norm_bsKernel_le {c : ℝ} (hc : 1 ≤ c) {z : Plane} (hq : |z.1| ≤ c / 2) (hz : z ≠ 0) :
    ‖bsKernel c z‖ ≤ (Real.sqrt (z.1 ^ 2 + z.2 ^ 2))⁻¹ + 1 := by
  have hz' : ((z.1 : ℂ) + (z.2 : ℂ) * I) ≠ 0 := by
    intro h
    apply hz
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    ext <;> simp [h1, h2]
  have hre : |((z.1 : ℂ) + (z.2 : ℂ) * I).re| ≤ c / 2 := by simpa using hq
  have h := Kernels.norm_cylinderBS_le' hc hre hz'
  rw [norm_bsKernel, bsC]
  have hn : ‖((z.1 : ℂ) + (z.2 : ℂ) * I)‖ = Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp
  rw [hn, one_mul] at h
  exact h

/-- **The cylinder Biot–Savart operator** `K_c ω (x) = ∫_cell ω(y) K_c(x − y) dy` (B0655). -/
def K (c : ℝ) (ω : Plane → ℝ) (x : Plane) : Vec2 := ∫ y in cell c, ω y • bsKernel c (x - y)

/-- `K_c ω` is `c`-periodic. -/
theorem isPeriodic_K (c : ℝ) (ω : Plane → ℝ) : IsPeriodic c (K c ω) := by
  intro x
  simp only [K]
  congr 1
  funext y
  congr 1
  have e : ((x.1 + c, x.2) : Plane) - y = ((x - y).1 + c, (x - y).2) := by
    ext <;> simp; ring
  rw [e, isPeriodic_bsKernel c (x - y)]

/-- **The centred form** of `K_c ω` for periodic `ω`: `K_c ω (x) = ∫_cell ω(x − y) K_c(y) dy`, so
the integration variable runs over the centred cell where the near/far bound
`norm_bsKernel_le` holds. -/
theorem K_eq_reflect (hc : 0 < c) {ω : Plane → ℝ} (hω : IsPeriodic c ω) (x : Plane) :
    K c ω x = ∫ y in cell c, ω (x - y) • bsKernel c y := by
  have hG : IsPeriodic c fun w => ω (x - w) • bsKernel c w := by
    intro w
    show ω (x - (w.1 + c, w.2)) • bsKernel c (w.1 + c, w.2) = ω (x - w) • bsKernel c w
    rw [isPeriodic_bsKernel c w]
    congr 1
    have := hω.sub_eq (x - w)
    rw [← this]
    congr 1
    ext <;> simp; ring
  have := integral_cell_comp_sub_left hc hG x
  simpa [K] using this

/-! ### The near/far split (B0658) -/

/-- The near part of the kernel on the cell: `K_c` on `cell c ∩ {‖y‖_∞ < 1}`. -/
def kNear (c : ℝ) : Plane → Vec2 := (cell c ∩ Metric.ball 0 1).indicator (bsKernel c)

/-- The far part of the kernel on the cell. -/
def kFar (c : ℝ) : Plane → Vec2 := (cell c \ Metric.ball 0 1).indicator (bsKernel c)

theorem sup_norm_le_euclid (y : Plane) : ‖y‖ ≤ Real.sqrt (y.1 ^ 2 + y.2 ^ 2) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  · rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)

/-- The pointwise near bound `‖K_c(y)‖ ≤ 2 ‖y‖_∞^{-1}` on `cell c ∩ {0 < ‖y‖_∞ < 1}`. -/
theorem norm_bsKernel_le_near {c : ℝ} (hc : 1 ≤ c) {y : Plane} (hy : y ∈ cell c)
    (h1 : ‖y‖ < 1) (h0 : y ≠ 0) : ‖bsKernel c y‖ ≤ 2 * ‖y‖ ^ (-1 : ℝ) := by
  have hq : |y.1| ≤ c / 2 := by
    rw [mem_cell] at hy; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 h0
  have h := norm_bsKernel_le hc hq h0
  have he := sup_norm_le_euclid y
  have hinv : (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ ≤ ‖y‖⁻¹ := inv_anti₀ hpos he
  have hone : (1 : ℝ) ≤ ‖y‖⁻¹ := by rw [le_inv_comm₀ one_pos hpos, inv_one]; exact h1.le
  rw [Real.rpow_neg_one]
  linarith

/-- The pointwise far bound `‖K_c(y)‖ ≤ 2` on `cell c ∩ {‖y‖_∞ ≥ 1}`. -/
theorem norm_bsKernel_le_far {c : ℝ} (hc : 1 ≤ c) {y : Plane} (hy : y ∈ cell c)
    (h1 : 1 ≤ ‖y‖) : ‖bsKernel c y‖ ≤ 2 := by
  have hq : |y.1| ≤ c / 2 := by
    rw [mem_cell] at hy; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have h0 : y ≠ 0 := by rintro rfl; norm_num at h1
  have h := norm_bsKernel_le hc hq h0
  have he := sup_norm_le_euclid y
  have hinv : (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]; linarith
  linarith

/-- **The kernel split** (B0658 tex 13917–13925): uniformly in `c ≥ 1`, on the cell
`K_c = k_near + k_far`, `∫_cell |k_near| ≤ C` and `|k_far| ≤ 2`. -/
theorem bsKernel_split : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c →
    (∫⁻ y in cell c, ‖kNear c y‖ₑ ≤ ENNReal.ofReal C) ∧ (∀ y, ‖kFar c y‖ ≤ 2) ∧
      ∀ y ∈ cell c, bsKernel c y = kNear c y + kFar c y := by
  set g : Plane → ℝ := fun y => 2 * ‖y‖ ^ (-1 : ℝ)
  have hgi : IntegrableOn g (Metric.ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 2) (α := 1) ?_ ?_ ?_ ?_
    · rw [Module.finrank_prod, Module.finrank_self]; norm_num
    · rw [Module.finrank_prod, Module.finrank_self]; norm_num
    · exact Eventually.of_forall fun y => by
        simp only [g, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  refine ⟨∫ y in Metric.ball 0 1, g y, setIntegral_nonneg Metric.isOpen_ball.measurableSet
    fun y _ => by positivity, fun c hc => ⟨?_, ?_, ?_⟩⟩
  · rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => by positivity)]
    have hmeas : MeasurableSet (cell c ∩ Metric.ball (0 : Plane) 1) :=
      (measurableSet_cell c).inter Metric.isOpen_ball.measurableSet
    calc ∫⁻ y in cell c, ‖kNear c y‖ₑ
        = ∫⁻ y in cell c ∩ Metric.ball 0 1, ‖bsKernel c y‖ₑ := by
          rw [kNear]
          simp_rw [enorm_indicator_eq_indicator_enorm]
          rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
          congr 2
          ext y; simp only [mem_inter_iff]; tauto
      _ ≤ ∫⁻ y in cell c ∩ Metric.ball 0 1, ENNReal.ofReal (g y) := by
          refine setLIntegral_mono_ae' hmeas ?_
          have hae : ∀ᵐ y ∂(volume : Measure Plane), y ≠ 0 := by
            rw [ae_iff]; simp [measure_singleton]
          filter_upwards [hae] with y h0 hy
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal (norm_bsKernel_le_near hc hy.1 ?_ h0)
          simpa using hy.2
      _ ≤ ∫⁻ y in Metric.ball 0 1, ENNReal.ofReal (g y) := lintegral_mono_set inter_subset_right
  · intro y
    by_cases hy : y ∈ cell c \ Metric.ball 0 1
    · rw [kFar, indicator_of_mem hy]
      refine norm_bsKernel_le_far hc hy.1 ?_
      have := hy.2
      simpa using this
    · rw [kFar, indicator_of_notMem hy, norm_zero]; norm_num
  · intro y hy
    by_cases hb : y ∈ Metric.ball (0 : Plane) 1
    · rw [kNear, kFar, indicator_of_mem (show y ∈ cell c ∩ Metric.ball 0 1 from ⟨hy, hb⟩),
        indicator_of_notMem (show y ∉ cell c \ Metric.ball 0 1 from fun h => h.2 hb), add_zero]
    · rw [kNear, kFar, indicator_of_notMem (show y ∉ cell c ∩ Metric.ball 0 1 from fun h => hb h.2),
        indicator_of_mem (show y ∈ cell c \ Metric.ball 0 1 from ⟨hy, hb⟩), zero_add]

/-! ### The operator split -/

theorem measurable_bsKernel (c : ℝ) : Measurable (bsKernel c) := by
  have hcot : Measurable Complex.cot := by
    have e : Complex.cot = fun z => Complex.cos z / Complex.sin z :=
      funext Complex.cot_eq_cos_div_sin
    rw [e]
    exact Complex.measurable_cos.div Complex.measurable_sin
  have h1 : Measurable (bsC c) := by
    unfold bsC Kernels.cylinderBS
    refine measurable_const.mul (measurable_const.mul (hcot.comp ?_))
    fun_prop
  unfold bsKernel
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => by
    fin_cases i
    · exact Complex.measurable_re.comp h1
    · exact (Complex.measurable_im.comp h1).neg)

/-- Minkowski on the cylinder with a vector kernel: for `c`-periodic real `f`,
`‖∫ f(· − y) k(y) dν(y)‖_{Lᵖ(cell)} ≤ (∫⁻ |k| dν) ‖f‖_{Lᵖ(cell)}`. -/
theorem eLpNorm_conv_periodic_le_vec {c : ℝ} (hc : 0 < c) {ν : Measure Plane} [SigmaFinite ν]
    {k : Plane → Vec2} {f : Plane → ℝ} (hk : StronglyMeasurable k) (hf : StronglyMeasurable f)
    (hper : IsPeriodic c f) {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun x => ∫ y, f (x - y) • k y ∂ν) p (cellμ c) ≤
      (∫⁻ y, ‖k y‖ₑ ∂ν) * eLpNorm f p (cellμ c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hF : AEStronglyMeasurable (Function.uncurry fun x y => f (x - y) • k y)
      ((cellμ c).prod ν) :=
    ((hf.comp_measurable (measurable_fst.sub measurable_snd)).smul
      (hk.comp_measurable measurable_snd)).aestronglyMeasurable
  refine (UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hF hp hp').trans (le_of_eq ?_)
  calc ∫⁻ y, eLpNorm (fun x => f (x - y) • k y) p (cellμ c) ∂ν
      = ∫⁻ y, ‖k y‖ₑ * eLpNorm f p (cellμ c) ∂ν := by
        congr 1
        funext y
        have e : eLpNorm (fun x => f (x - y) • k y) p (cellμ c) =
            eLpNorm (‖k y‖ • fun x => f (x - y)) p (cellμ c) :=
          eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
            simp only [Pi.smul_apply, norm_smul, norm_norm]; ring)
        rw [e, eLpNorm_const_smul, enorm_norm, eLpNorm_cell_comp_sub hc hper hp0 hp' y]
    _ = (∫⁻ y, ‖k y‖ₑ ∂ν) * eLpNorm f p (cellμ c) :=
        lintegral_mul_const _ hk.measurable.enorm

/-- The near part `u_near(x) = ∫_cell ω(x − y) k_near(y) dy`. -/
def uNear (c : ℝ) (ω : Plane → ℝ) (x : Plane) : Vec2 := ∫ y in cell c, ω (x - y) • kNear c y

/-- The far part `u_far(x) = ∫_cell ω(x − y) k_far(y) dy`. -/
def uFar (c : ℝ) (ω : Plane → ℝ) (x : Plane) : Vec2 := ∫ y in cell c, ω (x - y) • kFar c y

/-- **`K_split`** (B0658, tex 13917–13925: `K_c = k_near + k_far`, `‖K_c f‖_{L²+L^∞} ≤
C(‖f‖₁ + ‖f‖₂)`, uniformly for `c ≥ 1`): for `c`-periodic `ω`,
`‖u_near‖_{L²(cell)} ≤ C ‖ω‖_{L²(cell)}`, `|u_far| ≤ 2 ‖ω‖_{L¹(cell)}`, and
`K_c ω = u_near + u_far` at every `x` where both integrals converge. -/
theorem K_split : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ ω : Plane → ℝ, StronglyMeasurable ω →
    IsPeriodic c ω →
    eLpNorm (uNear c ω) 2 (cellμ c) ≤ ENNReal.ofReal C * eLpNorm ω 2 (cellμ c) ∧
    (∀ x, ‖uFar c ω x‖ₑ ≤ ENNReal.ofReal 2 * ∫⁻ y in cell c, ‖ω y‖ₑ) ∧
    ∀ x, Integrable (fun y => ω (x - y) • kNear c y) (volume.restrict (cell c)) →
      Integrable (fun y => ω (x - y) • kFar c y) (volume.restrict (cell c)) →
      K c ω x = uNear c ω x + uFar c ω x := by
  obtain ⟨C, hC0, hC⟩ := bsKernel_split
  refine ⟨C, hC0, fun c hc ω hω hper => ⟨?_, ?_, ?_⟩⟩
  · have hc0 : 0 < c := by linarith
    have hkn : StronglyMeasurable (kNear c) :=
      ((measurable_bsKernel c).indicator ((measurableSet_cell c).inter
        Metric.isOpen_ball.measurableSet)).stronglyMeasurable
    refine (eLpNorm_conv_periodic_le_vec hc0 (ν := volume.restrict (cell c)) hkn hω hper
      (by norm_num) (by norm_num)).trans ?_
    gcongr
    exact (hC c hc).1
  · intro x
    have hc0 : 0 < c := by linarith
    calc ‖uFar c ω x‖ₑ ≤ ∫⁻ y in cell c, ‖ω (x - y) • kFar c y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y in cell c, ENNReal.ofReal 2 * ‖ω (x - y)‖ₑ := by
          refine lintegral_mono fun y => ?_
          rw [enorm_smul, mul_comm, ← ofReal_norm_eq_enorm (kFar c y)]
          gcongr
          exact (hC c hc).2.1 y
      _ = ENNReal.ofReal 2 * ∫⁻ y in cell c, ‖ω (x - y)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal 2 * ∫⁻ y in cell c, ‖ω y‖ₑ := by
          rw [lintegral_cell_comp_sub_left hc0 (G := fun y => ‖ω y‖ₑ)
            (fun z => by simp only [hper z]) x]
  · intro x h1 h2
    have hc0 : 0 < c := by linarith
    rw [K_eq_reflect hc0 hper, uNear, uFar, ← integral_add h1 h2]
    refine setIntegral_congr_fun (measurableSet_cell c) fun y hy => ?_
    rw [(hC c hc).2.2 y hy, smul_add]

end UnforcedLeray.Cyl
