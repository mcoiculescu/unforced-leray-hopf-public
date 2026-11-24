import UnforcedLeray.Units.B0059
import UnforcedLeray.Lib.OperatorInputs.HilbertSchmidt

/-!
# B0061 helper: `g ↦ c (Kg)_i` is compact on `L²(⟨y⟩^{2M} dy)` for a decaying coefficient `c`

Helper for blueprint unit **B0061** (`paper/main.tex:1222`, compactness of
`A_E f = (Kf)·∇E₀` on `H^j_M`). Throughout `M > 1`, `L2w M = L²(⟨y⟩^{2M} dy) = H^0_M` (B0008),
`K` is the planar Biot–Savart operator of B0009 (`biotSavart g i = g ⋆ K_i`) and `c` is a
continuous coefficient with a weighted `L^∞` bound `⟨y⟩^M |c(y)| ≤ A` and `⟨y⟩^M c ∈ L²`
(`WCoeff M c`; every derivative of a Schwartz function qualifies, B0060 `Coeff.lean`).

**Result.** `mulK hM hc i : L2w M →L[ℂ] L2w M`, `g ↦ c (Kg)_i` (`coeFn_mulK`), is a compact
operator (`isCompactOperator_mulK`).

**Proof (a bypass of the manuscript's Rellich argument, tex 1222).** The manuscript truncates
`∇E₀` to a disk, applies `eq:st18-t00048` and Rellich there, and lets the disk grow. Here the
kernel is truncated instead, near its singularity: split `K_i = K_i 1_{|z| < r} + K_i 1_{|z| ≥ r}`
with `r = rₙ = 1/(n+1)` (`knear`, `kfar`).
* The far part has `|K_i 1_{|z| ≥ r}| ≤ (2πr)^{-1}`, so `g ↦ c (g ⋆ K_i 1_{|z| ≥ r})` is the
  integral operator on `L²(⟨y⟩^{2M} dy)` of the kernel
  `k(x, y) = c(x) K_i 1_{|·| ≥ r}(x - y) ⟨y⟩^{-2M}` with
  `|k(x, y)| ≤ (2πr)^{-1} |c(x)| ⟨y⟩^{-2M}`, which is square integrable for the product of the
  weighted measures because `c ∈ L²(⟨x⟩^{2M} dx)` and `⟨y⟩^{-2M} ∈ L²(⟨y⟩^{2M} dy)` (`M > 1`).
  It is Hilbert–Schmidt, hence compact (`Lib/OperatorInputs/HilbertSchmidt.lean`,
  `isCompactOperator_kernelOperator`).
* The near part: by Young (`L¹ ⋆ L² → L²`, B0059's `PlanarBS.Conv.eLpNorm_convAbs_le`),
  `‖⟨x⟩^M c (g ⋆ K_i 1_{|z| < r})‖₂ ≤ A ‖K_i 1_{|z| < r}‖₁ ‖g‖₂ ≤ A ‖K_i 1_{|z|<r}‖₁ ‖g‖_{L²_M}`,
  and `‖K_i 1_{|z| < r}‖₁ → 0` as `r → 0` by dominated convergence (`tendsto_lintegral_knear`).
So `mulK` is an operator-norm limit of compact operators, hence compact (Mathlib
`isClosed_setOf_isCompactOperator`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0061

open UnforcedLeray.B0008 UnforcedLeray.B0009

/-! ### Weighted coefficients -/

/-- A continuous coefficient `c` with `⟨y⟩^M |c(y)| ≤ A` for some `A ≥ 0` and `⟨y⟩^M c ∈ L²`. -/
structure WCoeff (M : ℝ) (c : ℂ → ℂ) : Prop where
  continuous : Continuous c
  sup : ∃ A : ℝ, 0 ≤ A ∧ ∀ y, bracket y ^ M * ‖c y‖ ≤ A
  memLp : MemLp (fun y => bracket y ^ M • c y) 2 volume

/-! ### Elements of `L²(⟨y⟩^{2M} dy)` are in `L¹ ∩ L²` -/

theorem eLpNorm_vol_le {M : ℝ} (hM : 0 ≤ M) (g : L2w M) :
    eLpNorm (g : ℂ → ℂ) 2 volume ≤ ENNReal.ofReal ‖g‖ := by
  refine (B0059.eLpNorm_le_weighted hM _).trans (le_of_eq ?_)
  rw [← eLpNorm_wMeasure, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)]

theorem memLp_vol {M : ℝ} (hM : 0 ≤ M) (g : L2w M) : MemLp (g : ℂ → ℂ) 2 volume :=
  ⟨(Lp.aestronglyMeasurable g).mono_ac (volume_ac M),
    (eLpNorm_vol_le hM g).trans_lt ENNReal.ofReal_lt_top⟩

/-! ### The kernel split at radius `rₙ = 1/(n+1)` -/

/-- The truncation radius `rₙ = 1/(n+1)`. -/
def rad (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem rad_pos (n : ℕ) : 0 < rad n := by unfold rad; positivity

theorem rad_le_one (n : ℕ) : rad n ≤ 1 := by
  unfold rad
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `K_i 1_{|z| < rₙ}`. -/
def knear (n : ℕ) (i : Fin 2) : ℂ → ℂ := (ball (0 : ℂ) (rad n)).indicator (kernel i)

/-- `K_i 1_{|z| ≥ rₙ}`. -/
def kfar (n : ℕ) (i : Fin 2) : ℂ → ℂ := (ball (0 : ℂ) (rad n))ᶜ.indicator (kernel i)

theorem knear_add_kfar (n : ℕ) (i : Fin 2) : knear n i + kfar n i = kernel i := by
  funext z
  simp only [Pi.add_apply, knear, kfar]
  exact indicator_self_add_compl_apply _ _ _

theorem measurable_knear (n : ℕ) (i : Fin 2) : Measurable (knear n i) :=
  (measurable_kernel i).indicator measurableSet_ball

theorem measurable_kfar (n : ℕ) (i : Fin 2) : Measurable (kfar n i) :=
  (measurable_kernel i).indicator measurableSet_ball.compl

/-- `|K_i 1_{|z| ≥ r}| ≤ (2πr)^{-1}`. -/
theorem norm_kfar_le (n : ℕ) (i : Fin 2) (z : ℂ) : ‖kfar n i z‖ ≤ (2 * Real.pi * rad n)⁻¹ := by
  have hr := rad_pos n
  by_cases hz : z ∈ ball (0 : ℂ) (rad n)
  · rw [kfar, indicator_of_notMem (Set.notMem_compl_iff.2 hz), norm_zero]
    positivity
  · rw [kfar, indicator_of_mem (mem_compl hz)]
    have h1 : rad n ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    exact (norm_kernel_le i z).trans (inv_anti₀ (by positivity) (by gcongr))

theorem integrable_knear (n : ℕ) (i : Fin 2) : Integrable (knear n i) volume :=
  ((integrableOn_kernel_ball i).mono_set (ball_subset_ball (rad_le_one n))).integrable_indicator
    measurableSet_ball

theorem norm_knear_le (n : ℕ) (i : Fin 2) (z : ℂ) :
    ‖knear n i z‖ₑ ≤ ‖(ball (0 : ℂ) 1).indicator (kernel i) z‖ₑ := by
  by_cases hz : z ∈ ball (0 : ℂ) (rad n)
  · rw [knear, indicator_of_mem hz,
      indicator_of_mem (ball_subset_ball (rad_le_one n) hz)]
  · rw [knear, indicator_of_notMem hz, enorm_zero]
    exact zero_le

/-- `‖K_i 1_{|z| < rₙ}‖₁ → 0` (dominated convergence). -/
theorem tendsto_lintegral_knear (i : Fin 2) :
    Tendsto (fun n => ∫⁻ z, ‖knear n i z‖ₑ) atTop (𝓝 0) := by
  have hfin : ∫⁻ z, ‖(ball (0 : ℂ) 1).indicator (kernel i) z‖ₑ ≠ ∞ :=
    ((integrableOn_kernel_ball i).integrable_indicator measurableSet_ball).2.ne
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
    rw [ae_iff]
    simp
  have h := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure ℂ))
    (F := fun n z => ‖knear n i z‖ₑ) (f := fun _ => 0)
    (fun z => ‖(ball (0 : ℂ) 1).indicator (kernel i) z‖ₑ)
    (fun n => (measurable_knear n i).enorm) (fun n => ae_of_all _ (norm_knear_le n i)) hfin
    (by
      filter_upwards [h0] with z hz
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hzp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hr : rad n < ‖z‖ := by
        refine lt_of_le_of_lt ?_ hN
        unfold rad
        gcongr
      have hzn : z ∉ ball (0 : ℂ) (rad n) := by
        simpa [mem_ball_zero_iff] using hr.le
      simp [knear, indicator_of_notMem hzn])
  simpa using h

/-! ### Near and far convolutions -/

/-- `g ⋆ K_i 1_{|z| < rₙ}`. -/
def nearConv (n : ℕ) (i : Fin 2) (g : ℂ → ℂ) : ℂ → ℂ :=
  convolution g (knear n i) (ContinuousLinearMap.mul ℂ ℂ) volume

/-- `g ⋆ K_i 1_{|z| ≥ rₙ}`. -/
def farConv (n : ℕ) (i : Fin 2) (g : ℂ → ℂ) : ℂ → ℂ :=
  convolution g (kfar n i) (ContinuousLinearMap.mul ℂ ℂ) volume

theorem farConv_exists {g : ℂ → ℂ} (hg : Integrable g volume) (n : ℕ) (i : Fin 2) (y : ℂ) :
    ConvolutionExistsAt g (kfar n i) y (ContinuousLinearMap.mul ℂ ℂ) volume := by
  refine Integrable.mono' (hg.norm.const_mul (2 * Real.pi * rad n)⁻¹) ?_ (ae_of_all _ fun t => ?_)
  · exact hg.aestronglyMeasurable.mul
      ((measurable_kfar n i).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · simp only [ContinuousLinearMap.mul_apply', norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_kfar_le _ _ _) (norm_nonneg _)

/-- `Kg = g ⋆ K_i 1_{|z| < r} + g ⋆ K_i 1_{|z| ≥ r}` almost everywhere, for `g ∈ L¹`. -/
theorem biotSavart_ae_eq_near_add_far {g : ℂ → ℂ} (hg : Integrable g volume) (n : ℕ)
    (i : Fin 2) : biotSavart g i =ᵐ[volume] nearConv n i g + farConv n i g := by
  filter_upwards [hg.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_knear n i)] with y hy
  rw [Pi.add_apply, biotSavart, ← knear_add_kfar n i]
  exact hy.distrib_add (farConv_exists hg n i y)

theorem aestronglyMeasurable_nearConv {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) (n : ℕ)
    (i : Fin 2) : AEStronglyMeasurable (nearConv n i g) volume :=
  (hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
    (measurable_knear n i).aestronglyMeasurable).integral_prod_right'

/-- Young `L¹ ⋆ L² → L²` for the near part. -/
theorem eLpNorm_nearConv_le {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) (n : ℕ)
    (i : Fin 2) :
    eLpNorm (nearConv n i g) 2 volume ≤ (∫⁻ z, ‖knear n i z‖ₑ) * eLpNorm g 2 volume := by
  have hpt : ∀ y, ‖nearConv n i g y‖ₑ ≤ PlanarBS.Conv.convAbs (knear n i) g y := by
    intro y
    rw [nearConv, convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    unfold PlanarBS.Conv.convAbs
    refine lintegral_congr fun t => ?_
    simp only [ContinuousLinearMap.mul_apply', enorm_mul]
    ring
  have hle : eLpNorm (nearConv n i g) 2 volume ≤
      eLpNorm (PlanarBS.Conv.convAbs (knear n i) g) 2 volume :=
    eLpNorm_mono_enorm fun y => (hpt y).trans_eq (enorm_eq_self _).symm
  exact hle.trans (PlanarBS.Conv.eLpNorm_convAbs_le (measurable_knear n i).aestronglyMeasurable
    hg (p := 2) one_le_two)

/-! ### The near term in the weighted norm -/

section Coeff

variable {M : ℝ} {c : ℂ → ℂ}

/-- `‖⟨x⟩^M c (g ⋆ K_i 1_{|z|<r})‖₂ ≤ A ‖K_i 1_{|z|<r}‖₁ ‖g‖₂`. -/
theorem near_term (hc : WCoeff M c) {A : ℝ} (hA : ∀ y, bracket y ^ M * ‖c y‖ ≤ A)
    {g : ℂ → ℂ} (hg : MemLp g 2 volume) (n : ℕ) (i : Fin 2) :
    MemLp (fun x => c x * nearConv n i g x) 2 (wMeasure M) ∧
      eLpNorm (fun x => c x * nearConv n i g x) 2 (wMeasure M) ≤
        ENNReal.ofReal A * ((∫⁻ z, ‖knear n i z‖ₑ) * eLpNorm g 2 volume) := by
  have hbd : eLpNorm (fun x => bracket x ^ M • (c x * nearConv n i g x)) 2 volume ≤
      ENNReal.ofReal A * ((∫⁻ z, ‖knear n i z‖ₑ) * eLpNorm g 2 volume) := by
    have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure ℂ)) (p := 2)
      (f := fun x => bracket x ^ M • (c x * nearConv n i g x)) (g := nearConv n i g) (c := A)
      (Eventually.of_forall fun x => by
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (Real.rpow_pos_of_pos (bracket_pos x) M).le,
          ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _))
    exact h1.trans (by gcongr; exact eLpNorm_nearConv_le hg.1 n i)
  have hmeas : AEStronglyMeasurable (fun x => bracket x ^ M • (c x * nearConv n i g x)) volume :=
    (continuous_bracket_rpow M).aestronglyMeasurable.smul
      (hc.continuous.aestronglyMeasurable.mul (aestronglyMeasurable_nearConv hg.1 n i))
  refine ⟨(memLp_wMeasure_iff M).2 ⟨hmeas, hbd.trans_lt ?_⟩, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (integrable_knear n i).2 hg.2)
  · rw [eLpNorm_wMeasure]
    exact hbd

/-! ### The far term: a Hilbert–Schmidt operator -/

/-- The kernel `k(x, y) = c(x) K_i 1_{|·| ≥ r}(x - y) ⟨y⟩^{-2M}` of `g ↦ c (g ⋆ K_i 1_{|z| ≥ r})`
on `L²(⟨y⟩^{2M} dy)`. -/
def hsKernel (M : ℝ) (c : ℂ → ℂ) (n : ℕ) (i : Fin 2) (z : ℂ × ℂ) : ℂ :=
  c z.1 * kfar n i (z.1 - z.2) * invWeight M z.2

theorem continuous_invWeight (M : ℝ) : Continuous (invWeight M) := by
  unfold invWeight
  exact Complex.continuous_ofReal.comp
    ((continuous_coe_density M).inv₀ fun y => (density_pos M y).ne')

/-- The far kernel is square integrable for the product of the weighted measures. -/
theorem memLp_hsKernel (hM : 1 < M) (hc : WCoeff M c) (n : ℕ) (i : Fin 2) :
    MemLp (hsKernel M c n i) 2 ((wMeasure M).prod (wMeasure M)) := by
  set C : ℝ := (2 * Real.pi * rad n)⁻¹ with hC
  have hC0 : 0 ≤ C := by have := rad_pos n; positivity
  have hcw : MemLp c 2 (wMeasure M) := (memLp_wMeasure_iff M).2 hc.memLp
  have hu : Integrable (fun x => ‖c x‖ ^ 2) (wMeasure M) :=
    (memLp_two_iff_integrable_sq_norm hcw.1).1 hcw
  have hv : Integrable (fun y => ‖invWeight M y‖ ^ 2) (wMeasure M) :=
    (memLp_two_iff_integrable_sq_norm (memLp_invWeight hM).1).1 (memLp_invWeight hM)
  have hprod := hu.mul_prod hv
  have hBmeas : AEStronglyMeasurable (fun z : ℂ × ℂ => ‖c z.1‖ * ‖invWeight M z.2‖)
      ((wMeasure M).prod (wMeasure M)) :=
    ((hc.continuous.norm.comp continuous_fst).mul
      ((continuous_invWeight M).norm.comp continuous_snd)).aestronglyMeasurable
  have hB : MemLp (fun z : ℂ × ℂ => ‖c z.1‖ * ‖invWeight M z.2‖) 2
      ((wMeasure M).prod (wMeasure M)) := by
    refine (memLp_two_iff_integrable_sq_norm hBmeas).2 (hprod.congr (ae_of_all _ fun z => ?_))
    simp only [norm_mul, norm_norm]
    ring
  have hkmeas : AEStronglyMeasurable (hsKernel M c n i) ((wMeasure M).prod (wMeasure M)) := by
    unfold hsKernel
    exact (((hc.continuous.measurable.comp measurable_fst).mul
      ((measurable_kfar n i).comp (measurable_fst.sub measurable_snd))).mul
      ((continuous_invWeight M).measurable.comp measurable_snd)).aestronglyMeasurable
  refine (hB.const_mul C).of_le hkmeas (ae_of_all _ fun z => ?_)
  show ‖hsKernel M c n i z‖ ≤ ‖C * (‖c z.1‖ * ‖invWeight M z.2‖)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [hsKernel, norm_mul]
  calc ‖c z.1‖ * ‖kfar n i (z.1 - z.2)‖ * ‖invWeight M z.2‖
      ≤ ‖c z.1‖ * C * ‖invWeight M z.2‖ := by
        gcongr
        exact norm_kfar_le n i _
    _ = C * (‖c z.1‖ * ‖invWeight M z.2‖) := by ring

theorem integral_hsKernel (n : ℕ) (i : Fin 2) (g : ℂ → ℂ) (x : ℂ) :
    ∫ y, hsKernel M c n i (x, y) * g y ∂(wMeasure M) = c x * farConv n i g x := by
  rw [integral_wMeasure, farConv, convolution_def, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hρ : ((density M y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (density_pos M y).ne'
  simp only [hsKernel, invWeight, ContinuousLinearMap.mul_apply', NNReal.smul_def,
    Complex.real_smul, Complex.ofReal_inv]
  field_simp

variable (M) in
/-- The Hilbert–Schmidt operator `g ↦ c (g ⋆ K_i 1_{|z| ≥ rₙ})` on `L²(⟨y⟩^{2M} dy)`. -/
def hsOp (hM : 1 < M) (hc : WCoeff M c) (n : ℕ) (i : Fin 2) : L2w M →L[ℂ] L2w M :=
  ExternalInputs.kernelOperator (memLp_hsKernel hM hc n i)

theorem isCompactOperator_hsOp (hM : 1 < M) (hc : WCoeff M c) (n : ℕ) (i : Fin 2) :
    IsCompactOperator (hsOp M hM hc n i) :=
  ExternalInputs.isCompactOperator_kernelOperator _

theorem coeFn_hsOp (hM : 1 < M) (hc : WCoeff M c) (n : ℕ) (i : Fin 2) (g : L2w M) :
    (hsOp M hM hc n i g : ℂ → ℂ) =ᵐ[wMeasure M] fun x => c x * farConv n i g x := by
  filter_upwards [ExternalInputs.coeFn_kernelOperator (memLp_hsKernel hM hc n i) g] with x hx
  rw [hsOp, hx, integral_hsKernel]

/-! ### The operator `g ↦ c (Kg)_i` -/

theorem ae_mulK_eq (hM : 1 < M) (hc : WCoeff M c) (n : ℕ) (i : Fin 2) (g : L2w M) :
    (fun x => c x * biotSavart g i x) =ᵐ[wMeasure M]
      (fun x => c x * nearConv n i g x) + (hsOp M hM hc n i g : ℂ → ℂ) := by
  filter_upwards [(wMeasure_ac M).ae_le
      (biotSavart_ae_eq_near_add_far (integrable_L2w hM g) n i), coeFn_hsOp hM hc n i g]
    with x h1 h2
  rw [Pi.add_apply, h2, h1, Pi.add_apply, mul_add]

theorem memLp_mulK (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (g : L2w M) :
    MemLp (fun x => c x * biotSavart g i x) 2 (wMeasure M) := by
  obtain ⟨A, -, hA⟩ := hc.sup
  have h1 := (near_term hc hA (memLp_vol (by linarith) g) 0 i).1
  exact (h1.add (Lp.memLp (hsOp M hM hc 0 i g))).ae_eq (ae_mulK_eq hM hc 0 i g).symm

variable (M) in
/-- `g ↦ c (Kg)_i` as a map `L²(⟨y⟩^{2M} dy) → L²(⟨y⟩^{2M} dy)`. -/
def mulKFun (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (g : L2w M) : L2w M :=
  (memLp_mulK hM hc i g).toLp _

theorem coeFn_mulKFun (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (g : L2w M) :
    (mulKFun M hM hc i g : ℂ → ℂ) =ᵐ[wMeasure M] fun x => c x * biotSavart g i x :=
  MemLp.coeFn_toLp _

/-- `‖c (Kg)_i - c (g ⋆ K_i 1_{|z| ≥ rₙ})‖_{L²_M} ≤ A ‖K_i 1_{|z| < rₙ}‖₁ ‖g‖_{L²_M}`. -/
theorem norm_mulKFun_sub_hsOp_le (hM : 1 < M) (hc : WCoeff M c) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ y, bracket y ^ M * ‖c y‖ ≤ A) (n : ℕ) (i : Fin 2) (g : L2w M) :
    ‖mulKFun M hM hc i g - hsOp M hM hc n i g‖ ≤
      A * (∫⁻ z, ‖knear n i z‖ₑ).toReal * ‖g‖ := by
  have hM0 : 0 ≤ M := by linarith
  have hnear := near_term hc hA (memLp_vol hM0 g) n i
  have hae : ((mulKFun M hM hc i g - hsOp M hM hc n i g : L2w M) : ℂ → ℂ) =ᵐ[wMeasure M]
      fun x => c x * nearConv n i g x := by
    filter_upwards [Lp.coeFn_sub (mulKFun M hM hc i g) (hsOp M hM hc n i g),
      coeFn_mulKFun hM hc i g, ae_mulK_eq hM hc n i g] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.add_apply, add_sub_cancel_right]
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have hfin : (∫⁻ z, ‖knear n i z‖ₑ) ≠ ∞ := (integrable_knear n i).2.ne
  calc (eLpNorm (fun x => c x * nearConv n i g x) 2 (wMeasure M)).toReal
      ≤ (ENNReal.ofReal A * ((∫⁻ z, ‖knear n i z‖ₑ) * ENNReal.ofReal ‖g‖)).toReal := by
        refine ENNReal.toReal_mono (by finiteness) (hnear.2.trans ?_)
        gcongr
        exact eLpNorm_vol_le hM0 g
    _ = A * (∫⁻ z, ‖knear n i z‖ₑ).toReal * ‖g‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0,
          ENNReal.toReal_ofReal (norm_nonneg _)]
        ring

theorem mulKFun_add (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (g h : L2w M) :
    mulKFun M hM hc i (g + h) = mulKFun M hM hc i g + mulKFun M hM hc i h := by
  apply Lp.ext
  have h2 : ((g + h : L2w M) : ℂ → ℂ) =ᵐ[volume] (g : ℂ → ℂ) + (h : ℂ → ℂ) :=
    (volume_ac M).ae_le (Lp.coeFn_add _ _)
  have h3 : biotSavart (g + h : L2w M) i =ᵐ[wMeasure M] biotSavart g i + biotSavart h i := by
    rw [biotSavart_congr_ae h2 i]
    exact (wMeasure_ac M).ae_le (biotSavart_add_ae (integrable_L2w hM g) (integrable_L2w hM h) i)
  filter_upwards [coeFn_mulKFun hM hc i (g + h), h3, Lp.coeFn_add (mulKFun M hM hc i g)
    (mulKFun M hM hc i h), coeFn_mulKFun hM hc i g, coeFn_mulKFun hM hc i h]
    with x e1 e3 e4 e5 e6
  rw [e1, e4, Pi.add_apply, e5, e6, e3, Pi.add_apply, mul_add]

theorem mulKFun_smul (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (a : ℂ) (g : L2w M) :
    mulKFun M hM hc i (a • g) = a • mulKFun M hM hc i g := by
  apply Lp.ext
  have h2 : ((a • g : L2w M) : ℂ → ℂ) =ᵐ[volume] a • (g : ℂ → ℂ) :=
    (volume_ac M).ae_le (Lp.coeFn_smul _ _)
  filter_upwards [coeFn_mulKFun hM hc i (a • g), Lp.coeFn_smul a (mulKFun M hM hc i g),
    coeFn_mulKFun hM hc i g] with x e1 e4 e5
  rw [e1, e4, Pi.smul_apply, e5, biotSavart_congr_ae h2 i, biotSavart_smul, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  ring

variable (M) in
/-- **The operator `g ↦ c (Kg)_i` on `L²(⟨y⟩^{2M} dy)`**, bounded (`M > 1`, `c` a weighted
coefficient). -/
def mulK (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) : L2w M →L[ℂ] L2w M :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := mulKFun M hM hc i
      map_add' := mulKFun_add hM hc i
      map_smul' := fun a g => by
        rw [RingHom.id_apply]
        exact mulKFun_smul hM hc i a g }
    (by
      obtain ⟨A, hA0, hA⟩ := hc.sup
      refine ⟨‖hsOp M hM hc 0 i‖ + A * (∫⁻ z, ‖knear 0 i z‖ₑ).toReal, fun g => ?_⟩
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖mulKFun M hM hc i g‖
          ≤ ‖hsOp M hM hc 0 i g‖ + ‖mulKFun M hM hc i g - hsOp M hM hc 0 i g‖ :=
            norm_le_insert' _ _
        _ ≤ ‖hsOp M hM hc 0 i‖ * ‖g‖ + A * (∫⁻ z, ‖knear 0 i z‖ₑ).toReal * ‖g‖ :=
            add_le_add ((hsOp M hM hc 0 i).le_opNorm g)
              (norm_mulKFun_sub_hsOp_le hM hc hA0 hA 0 i g)
        _ = _ := by ring)

theorem mulK_apply (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (g : L2w M) :
    mulK M hM hc i g = mulKFun M hM hc i g := rfl

/-- `mulK` is multiplication of the velocity component `(Kg)_i` by `c`. -/
theorem coeFn_mulK (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) (g : L2w M) :
    (mulK M hM hc i g : ℂ → ℂ) =ᵐ[volume] fun x => c x * biotSavart g i x :=
  (volume_ac M).ae_le (coeFn_mulKFun hM hc i g)

/-- **`g ↦ c (Kg)_i` is a compact operator on `L²(⟨y⟩^{2M} dy)`** (`M > 1`; tex 1222 at the
level of one Leibniz term). -/
theorem isCompactOperator_mulK (hM : 1 < M) (hc : WCoeff M c) (i : Fin 2) :
    IsCompactOperator (mulK M hM hc i) := by
  obtain ⟨A, hA0, hA⟩ := hc.sup
  have hL : Tendsto (fun n => A * (∫⁻ z, ‖knear n i z‖ₑ).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_lintegral_knear i)
    simpa using h.const_mul A
  have hT : Tendsto (fun n => hsOp M hM hc n i) atTop (𝓝 (mulK M hM hc i)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hA0 ENNReal.toReal_nonneg) fun g => ?_
    rw [show (hsOp M hM hc n i - mulK M hM hc i) g = hsOp M hM hc n i g - mulK M hM hc i g
      from rfl, norm_sub_rev, mulK_apply]
    exact norm_mulKFun_sub_hsOp_le hM hc hA0 hA n i g
  exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto hT
    (Eventually.of_forall fun n => isCompactOperator_hsOp hM hc n i)

end Coeff

end UnforcedLeray.B0061
