import UnforcedLeray.Units.B0009
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Young
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# B0059 (helper): Biot–Savart bounds on the weighted spaces, conditional form

Helper of `Units/B0059.lean` (blueprint unit **B0059**, label `eq:st18-t00048`,
`paper/main.tex` lines 1206–1213, proof of "Compactness of the Euler interaction", section
`sec:st18-1373`). Everything here is proved; the results of positive derivative order take the
first-order `L²` bound as the hypothesis `GradL2Bound C`, which `Units/B0059/GradL2.lean`
discharges (with `C = 2`) from the transported NonUniqueEuler proof; `Units/B0059.lean` states the
unit unconditionally.

**Statement (tex 1206–1213).** Since `M > 1`, `‖f‖₁ ≤ C_M ‖f‖_{L²_M}`. Split the Biot–Savart
kernel smoothly at distance one: the near part is in `L¹`, so it maps `L²` to `L²`; the far part is
bounded, so it maps `L¹` to `L^∞`. For derivatives of positive order the Fourier multiplier of
`∂^α K` has order `|α| - 1` with bounded angular multiplier. Consequently
`‖∂^α K f‖₂ ≤ C_α ‖f‖_{H^{|α|-1}}` for `|α| ≥ 1`, and `‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`.
No global weighted velocity estimate is inferred.

**Conventions.** As in B0008/B0009 (`UnforcedLeray.B0008`, `UnforcedLeray.B0009`): the plane is
`ℂ` with Lebesgue measure, `f` is complex, `Kf` has the two complex components
`biotSavart f 0`, `biotSavart f 1` (convolutions with `kernel i z = (z^⊥)_i/(2π|z|²)`).
Weak derivatives, `H^k(V)`, `‖·‖_{H^k(V)}` are those of the vendored
`NonUniqueEuler.Defs.Infra.Sobolev` (`HasWeakDerivOn`, `MemHOn`, `normHOn`, `MemH`, `normH`,
`weakPartial`, `l2`), so `‖f‖_{H^{|α|-1}}` is the unweighted Sobolev norm of the manuscript.

**The smooth split (tex 1207).** `cutoff` is a `C^∞_c` bump, `1` on `|z| ≤ 1/2` and `0` on
`|z| ≥ 1`; `nearKernel i = cutoff · K_i`, `farKernel i = (1 - cutoff) · K_i`. The near part is
integrable (`integrable_nearKernel`), and Young's inequality `L¹ ⋆ L² → L²`
(`UnforcedLeray.PlanarBS.Conv.eLpNorm_convAbs_le`, the transported NonUniqueEuler
`P/Infra/ConvMinkowski/Young.lean`) gives `memLp_nearPart`; the far part is bounded by `1/π`
(`norm_farKernel_le`), so `norm_farPart_le`: `‖f ⋆ K_far‖_∞ ≤ π⁻¹ ‖f‖₁`.

**Derivatives (tex 1208–1211).** The commutation `∂^β (Kf) = K(∂^β f)` (weakly, for `f`,
`∂^β f ∈ L¹`) is proved here (`hasWeakDerivOn_biotSavart`) by Fubini against the split kernel and
translation of test functions. The first-order `L²` bound `‖∂_k (Kg)_i‖₂ ≤ C ‖g‖₂` for
`g ∈ L¹ ∩ L²` is the Fourier-multiplier (Plancherel / Calderón–Zygmund) fact of the manuscript's
sentence "the Fourier multiplier of `∂^α K` has order `|α| - 1` with bounded angular multiplier"
in its base case `|α| = 1`; here it is the hypothesis `GradL2Bound C` (blueprint infrastructure
INF21, "Plancherel and `L²` Fourier multipliers"), proved in `Units/B0059/GradL2.lean`. The higher orders follow from it and the commutation
with constant `C_α = C` (`exists_weakDeriv_biotSavart`,
`l2_weakPartial_biotSavart_le_of_gradL2Bound`).

**Local bound (tex 1211).** `memHOn_biotSavart_ball_of_gradL2Bound`: for every `R` there is `C_{j,M,R}` with
`Kf ∈ H^{j+1}(B_R)` and `‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}` on `H^j_M`, `M > 1`.

Junk values: `Kf` is a Bochner integral (`0` where it diverges); it converges absolutely a.e. for
integrable `f` (B0009). All `L¹` statements carry integrability hypotheses; `normH`/`normHOn` are
used only together with the corresponding `MemH`/`MemHOn` (`memH_value`,
`memHOn_biotSavart_ball_of_gradL2Bound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.B0059

open NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0009

/-! ### The `L¹` bound on `L²_M` (tex 1206) -/

/-- **`‖f‖₁ ≤ C_M ‖f‖_{L²_M}` for `M > 1`** (`paper/main.tex:1206`, B0059; B0008's
`integral_norm_le` for functions): if `⟨y⟩^M f ∈ L²`, then `f ∈ L¹` and
`∫ |f| ≤ C_M ‖⟨y⟩^M f‖₂` with `C_M = (∫ ⟨y⟩^{-2M})^{1/2}`. -/
theorem integrable_and_integral_norm_le {M : ℝ} (hM : 1 < M) {f : ℂ → ℂ}
    (hf : MemLp (fun y => bracket y ^ M • f y) 2 volume) :
    Integrable f volume ∧
      ∫ y, ‖f y‖ ≤ CM M * (eLpNorm (fun y => bracket y ^ M • f y) 2 volume).toReal := by
  have hw : MemLp f 2 (wMeasure M) := (memLp_wMeasure_iff M).2 hf
  have hF : (hw.toLp f : ℂ → ℂ) =ᵐ[volume] f := coeFn_toLp_volume hw
  refine ⟨(integrable_L2w hM _).congr hF, ?_⟩
  have h1 := integral_norm_le hM (hw.toLp f)
  rw [norm_L2w] at h1
  have e1 : ∫ y, ‖(hw.toLp f : ℂ → ℂ) y‖ = ∫ y, ‖f y‖ :=
    integral_congr_ae (hF.mono fun y hy => by simp only [hy])
  have e2 : eLpNorm (fun y => bracket y ^ M • (hw.toLp f : ℂ → ℂ) y) 2 volume =
      eLpNorm (fun y => bracket y ^ M • f y) 2 volume :=
    eLpNorm_congr_ae (hF.mono fun y hy => by simp only [hy])
  rwa [e1, e2] at h1

/-- The same bound on `H^j_M`: `∫ |f| ≤ C_M ‖f‖_{H^j_M}`. -/
theorem integral_norm_value_le {j : ℕ} {M : ℝ} (hM : 1 < M) (F : HjM j M) :
    ∫ y, ‖F.value y‖ ≤ CM M * ‖F‖ :=
  (integral_norm_le hM F.value).trans
    (mul_le_mul_of_nonneg_left (HjM.norm_value_le F) (Real.sqrt_nonneg _))

/-! ### The weight is at least one -/

theorem one_le_bracket (y : ℂ) : 1 ≤ bracket y := by
  rw [bracket]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖y‖])

theorem one_le_bracket_rpow {M : ℝ} (hM : 0 ≤ M) (y : ℂ) : 1 ≤ bracket y ^ M :=
  Real.one_le_rpow (one_le_bracket y) hM

/-- `‖u‖₂ ≤ ‖⟨y⟩^M u‖₂` for `M ≥ 0`. -/
theorem eLpNorm_le_weighted {M : ℝ} (hM : 0 ≤ M) (u : ℂ → ℂ) :
    eLpNorm u 2 volume ≤ eLpNorm (fun y => bracket y ^ M • u y) 2 volume := by
  refine eLpNorm_mono fun y => ?_
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_pos_of_pos (bracket_pos y) M).le]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_bracket_rpow hM y)

namespace HjM

variable {j : ℕ} {M : ℝ}

/-- For `M ≥ 0` every stored derivative `∂^α f` of `f ∈ H^j_M` lies in the unweighted `L²`. -/
theorem memLp_der_volume (hM : 0 ≤ M) (F : B0008.HjM j M) (α : Idx j) :
    MemLp (F.der α : ℂ → ℂ) 2 volume :=
  ⟨(Lp.aestronglyMeasurable (F.der α)).mono_ac (volume_ac M),
    (eLpNorm_le_weighted hM _).trans_lt (F.memLp_der α).2⟩

theorem norm_der_le (F : B0008.HjM j M) (α : Idx j) : ‖F.der α‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : Tuple j M) α

/-- `‖∂^α f‖₂ ≤ ‖f‖_{H^j_M}` for `M ≥ 0`. -/
theorem eLpNorm_der_le (hM : 0 ≤ M) (F : B0008.HjM j M) (α : Idx j) :
    eLpNorm (F.der α : ℂ → ℂ) 2 volume ≤ ENNReal.ofReal ‖F‖ := by
  refine (eLpNorm_le_weighted hM _).trans ?_
  have hfin := (F.memLp_der α).2.ne
  rw [← ENNReal.ofReal_toReal hfin, ← norm_L2w]
  exact ENNReal.ofReal_le_ofReal (norm_der_le F α)

/-- `f ∈ H^j_M` with `M ≥ 0` lies in the unweighted `H^j` (`MemH j f`), so the unweighted norms
`‖f‖_{H^m}`, `m ≤ j`, of tex 1210 are meaningful. -/
theorem memH_value (hM : 0 ≤ M) (F : B0008.HjM j M) : MemH j (F.value : ℂ → ℂ) :=
  memH_iff.2 ⟨memLp_der_volume hM F (idx0 j), fun γ hγ =>
    ⟨F.der ⟨γ, hγ⟩, memLp_der_volume hM F _, F.hasWeakDeriv ⟨γ, hγ⟩⟩⟩

/-- The chosen weak derivative `∂^β f` (`weakPartial`) has the `L²` norm of the stored one. -/
theorem l2_weakPartial_value (F : B0008.HjM j M) (β : Idx j) :
    l2 (weakPartial β.1 (F.value : ℂ → ℂ)) = (eLpNorm (F.der β : ℂ → ℂ) 2 volume).toReal := by
  have h := weakDerivOn_ae_eq isOpen_univ
    ((locallyIntegrable_L2w M (F.der β)).locallyIntegrableOn univ) (F.hasWeakDeriv β)
  have hae : weakPartial β.1 (F.value : ℂ → ℂ) =ᵐ[volume] (F.der β : ℂ → ℂ) := by
    filter_upwards [h] with x hx using hx (mem_univ x)
  rw [l2, eLpNorm_congr_ae hae]

end HjM

/-- One term of the sum of squares is at most the `H^m` norm. -/
theorem l2_weakPartial_le_normH {m : ℕ} {β : ℕ × ℕ} (hβ : β ∈ multiIdx m) (f : ℂ → ℂ) :
    l2 (weakPartial β f) ≤ normH m f := by
  rw [normH_eq]
  have h := Finset.single_le_sum (f := fun γ => l2 (weakPartial γ f) ^ 2)
    (fun _ _ => sq_nonneg _) hβ
  simpa [abs_of_nonneg (l2_nonneg _)] using Real.abs_le_sqrt h

/-! ### The smooth split of the kernel at distance one (tex 1206–1207) -/

/-- The bump used for the split: `1` on `|z| ≤ 1/2`, `0` on `|z| ≥ 1`. -/
def cutoffBump : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The smooth cutoff `χ ∈ C^∞_c(ℝ²)`, `0 ≤ χ ≤ 1`, `χ = 1` on `|z| ≤ 1/2`, `χ = 0` on
`|z| ≥ 1` ("split the Biot–Savart kernel smoothly at distance one", tex 1206). -/
def cutoff (z : ℂ) : ℝ := cutoffBump z

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff := cutoffBump.contDiff

theorem hasCompactSupport_cutoff : HasCompactSupport cutoff := cutoffBump.hasCompactSupport

theorem cutoff_nonneg (z : ℂ) : 0 ≤ cutoff z := cutoffBump.nonneg' z

theorem cutoff_le_one (z : ℂ) : cutoff z ≤ 1 := cutoffBump.le_one

theorem cutoff_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : cutoff z = 1 :=
  cutoffBump.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz)

theorem cutoff_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : cutoff z = 0 :=
  cutoffBump.zero_of_le_dist (by rw [dist_zero_right]; exact hz)

theorem measurable_cutoff : Measurable cutoff := contDiff_cutoff.continuous.measurable

/-- The near part `χ K_i` of the Biot–Savart kernel (supported in `|z| < 1`). -/
def nearKernel (i : Fin 2) (z : ℂ) : ℂ := (cutoff z : ℂ) * kernel i z

/-- The far part `(1 - χ) K_i` of the Biot–Savart kernel (vanishing on `|z| ≤ 1/2`). -/
def farKernel (i : Fin 2) (z : ℂ) : ℂ := ((1 - cutoff z : ℝ) : ℂ) * kernel i z

theorem nearKernel_add_farKernel (i : Fin 2) : nearKernel i + farKernel i = kernel i := by
  funext z
  simp only [Pi.add_apply, nearKernel, farKernel]
  push_cast
  ring

theorem measurable_nearKernel (i : Fin 2) : Measurable (nearKernel i) :=
  (Complex.measurable_ofReal.comp measurable_cutoff).mul (measurable_kernel i)

theorem measurable_farKernel (i : Fin 2) : Measurable (farKernel i) :=
  (Complex.measurable_ofReal.comp (measurable_const.sub measurable_cutoff)).mul
    (measurable_kernel i)

theorem norm_nearKernel_le (i : Fin 2) (z : ℂ) :
    ‖nearKernel i z‖ ≤ ‖(ball (0 : ℂ) 1).indicator (kernel i) z‖ := by
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem hz, nearKernel, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (cutoff_nonneg z)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one z)
  · have h1 : 1 ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    rw [nearKernel, cutoff_eq_zero h1]
    simp

/-- **The near part is in `L¹`** (tex 1207). -/
theorem integrable_nearKernel (i : Fin 2) : Integrable (nearKernel i) volume :=
  ((integrableOn_kernel_ball i).integrable_indicator measurableSet_ball).mono
    (measurable_nearKernel i).aestronglyMeasurable (ae_of_all _ (norm_nearKernel_le i))

/-- **The far part is bounded**: `|K_far| ≤ 1/π` (tex 1207). -/
theorem norm_farKernel_le (i : Fin 2) (z : ℂ) : ‖farKernel i z‖ ≤ Real.pi⁻¹ := by
  by_cases hz : ‖z‖ ≤ 1 / 2
  · rw [farKernel, cutoff_eq_one hz]
    simp only [sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  · replace hz := not_le.1 hz
    have h0 : 0 ≤ 1 - cutoff z := sub_nonneg.2 (cutoff_le_one z)
    have h1 : 1 - cutoff z ≤ 1 := by linarith [cutoff_nonneg z]
    rw [farKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    calc (1 - cutoff z) * ‖kernel i z‖ ≤ 1 * (2 * Real.pi * ‖z‖)⁻¹ :=
          mul_le_mul h1 (norm_kernel_le i z) (norm_nonneg _) zero_le_one
      _ ≤ Real.pi⁻¹ := by
          rw [one_mul]
          exact inv_anti₀ Real.pi_pos (by nlinarith [Real.pi_pos])

/-! ### Near and far parts of `Kf` -/

/-- `f ⋆ K_near`, component `i`. -/
def nearPart (f : ℂ → ℂ) (i : Fin 2) : ℂ → ℂ :=
  convolution f (nearKernel i) (ContinuousLinearMap.mul ℂ ℂ) volume

/-- `f ⋆ K_far`, component `i`. -/
def farPart (f : ℂ → ℂ) (i : Fin 2) : ℂ → ℂ :=
  convolution f (farKernel i) (ContinuousLinearMap.mul ℂ ℂ) volume

theorem farPart_exists {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2) (y : ℂ) :
    ConvolutionExistsAt f (farKernel i) y (ContinuousLinearMap.mul ℂ ℂ) volume := by
  refine Integrable.mono' (hf.norm.const_mul Real.pi⁻¹) ?_ (ae_of_all _ fun t => ?_)
  · exact hf.aestronglyMeasurable.mul
      ((measurable_farKernel i).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · simp only [ContinuousLinearMap.mul_apply', norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_farKernel_le _ _) (norm_nonneg _)

/-- **The far part maps `L¹` to `L^∞`** (tex 1207): `|f ⋆ K_far| ≤ π⁻¹ ‖f‖₁` everywhere. -/
theorem norm_farPart_le {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2) (y : ℂ) :
    ‖farPart f i y‖ ≤ Real.pi⁻¹ * ∫ t, ‖f t‖ := by
  rw [farPart, convolution_def, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (ae_of_all _ fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_farKernel_le _ _) (norm_nonneg _)

theorem aestronglyMeasurable_farPart {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume)
    (i : Fin 2) : AEStronglyMeasurable (farPart f i) volume :=
  (hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
    (measurable_farKernel i).aestronglyMeasurable).integral_prod_right'

theorem aestronglyMeasurable_nearPart {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume)
    (i : Fin 2) : AEStronglyMeasurable (nearPart f i) volume :=
  (hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
    (measurable_nearKernel i).aestronglyMeasurable).integral_prod_right'

theorem memLp_top_farPart {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2) :
    MemLp (farPart f i) ⊤ volume :=
  memLp_top_of_bound (aestronglyMeasurable_farPart hf.aestronglyMeasurable i) _
    (ae_of_all _ (norm_farPart_le hf i))

/-- `Kf = f ⋆ K_near + f ⋆ K_far` almost everywhere, for `f ∈ L¹`. -/
theorem biotSavart_ae_eq_near_add_far {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2) :
    biotSavart f i =ᵐ[volume] nearPart f i + farPart f i := by
  filter_upwards [hf.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_nearKernel i)] with y hy
  rw [Pi.add_apply, biotSavart, ← nearKernel_add_farKernel i]
  exact hy.distrib_add (farPart_exists hf i y)

theorem enorm_nearPart_le (f : ℂ → ℂ) (i : Fin 2) (y : ℂ) :
    ‖nearPart f i y‖ₑ ≤ PlanarBS.Conv.convAbs (nearKernel i) f y := by
  rw [nearPart, convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  unfold PlanarBS.Conv.convAbs
  refine lintegral_congr fun t => ?_
  simp only [ContinuousLinearMap.mul_apply', enorm_mul]
  ring

/-- **The near part maps `L²` to `L²`** (tex 1207, Young `L¹ ⋆ L² → L²`):
`‖f ⋆ K_near‖₂ ≤ ‖K_near‖₁ ‖f‖₂`. -/
theorem memLp_nearPart {f : ℂ → ℂ} (hf : MemLp f 2 volume) (i : Fin 2) :
    MemLp (nearPart f i) 2 volume ∧
      eLpNorm (nearPart f i) 2 volume ≤ (∫⁻ z, ‖nearKernel i z‖ₑ) * eLpNorm f 2 volume := by
  have hle : eLpNorm (nearPart f i) 2 volume ≤
      eLpNorm (PlanarBS.Conv.convAbs (nearKernel i) f) 2 volume :=
    eLpNorm_mono_enorm fun y => (enorm_nearPart_le f i y).trans_eq (enorm_eq_self _).symm
  have hY := PlanarBS.Conv.eLpNorm_convAbs_le (measurable_nearKernel i).aestronglyMeasurable
    hf.1 (p := 2) one_le_two
  refine ⟨⟨aestronglyMeasurable_nearPart hf.1 i, ?_⟩, hle.trans hY⟩
  exact lt_of_le_of_lt (hle.trans hY) (ENNReal.mul_lt_top (integrable_nearKernel i).2 hf.2)

/-- For `f ∈ L¹ ∩ L²`, `Kf` is locally integrable (so its weak derivatives make sense). -/
theorem locallyIntegrable_biotSavart {f : ℂ → ℂ} (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume) (i : Fin 2) : LocallyIntegrable (biotSavart f i) volume :=
  (((memLp_nearPart hf2 i).1.locallyIntegrable one_le_two).add
    ((memLp_top_farPart hf1 i).locallyIntegrable le_top)).congr
    (biotSavart_ae_eq_near_add_far hf1 i).symm

/-- The local `L²` bound of `Kf` from the split: on every ball,
`‖Kf‖_{L²(B_R)} ≤ ‖K_near‖₁ ‖f‖₂ + |B_R|^{1/2} π⁻¹ ‖f‖₁`. -/
theorem eLpNorm_biotSavart_ball_le {f : ℂ → ℂ} (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume) (i : Fin 2) (R : ℝ) :
    eLpNorm (biotSavart f i) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      (∫⁻ z, ‖nearKernel i z‖ₑ) * eLpNorm f 2 volume +
        volume (ball (0 : ℂ) R) ^ (2 : ℝ≥0∞).toReal⁻¹ *
          ENNReal.ofReal (Real.pi⁻¹ * ∫ t, ‖f t‖) := by
  rw [eLpNorm_congr_ae (ae_restrict_of_ae (biotSavart_ae_eq_near_add_far hf1 i))]
  refine (eLpNorm_add_le (aestronglyMeasurable_nearPart hf2.1 i).restrict
    (aestronglyMeasurable_farPart hf1.aestronglyMeasurable i).restrict one_le_two).trans ?_
  refine add_le_add ((eLpNorm_restrict_le _ _ _ _).trans (memLp_nearPart hf2 i).2) ?_
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (ball (0 : ℂ) R)) (p := 2)
    (ae_of_all _ (norm_farPart_le hf1 i))
  rwa [Measure.restrict_apply_univ] at h

/-! ### Commuting derivatives with `K` (tex 1208–1210) -/

theorem iterDirDeriv_comp_add_right (w : ℂ) (vs : List ℂ) (φ : ℂ → ℂ) :
    iterDirDeriv vs (fun z => φ (z + w)) = fun z => iterDirDeriv vs φ (z + w) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext z
    rw [iterDirDeriv_cons, iterDirDeriv_cons, ih]
    simp only [dirDeriv]
    rw [fderiv_comp_add_right]

theorem isTestFn_comp_add_right {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (w : ℂ) :
    IsTestFn univ (fun z => φ (z + w)) :=
  ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
    hφ.compact.comp_homeomorph (Homeomorph.addRight w), subset_univ _⟩

/-- A weak derivative is translation invariant:
`∫ f(y - w) ∂_{vs}φ(y) dy = (-1)^{|vs|} ∫ g(y - w) φ(y) dy` when `∂_{vs} f = g` weakly. -/
theorem integral_translate_weakDeriv {vs : List ℂ} {f g : ℂ → ℂ}
    (h : HasWeakDerivOn univ vs f g) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (w : ℂ) :
    ∫ y, f (y - w) * iterDirDeriv vs φ y = (-1 : ℂ) ^ vs.length * ∫ y, g (y - w) * φ y := by
  have e1 : ∫ y, f (y - w) * iterDirDeriv vs φ y =
      ∫ x, f x * iterDirDeriv vs (fun z => φ (z + w)) x := by
    rw [iterDirDeriv_comp_add_right,
      ← integral_add_right_eq_self (fun y => f (y - w) * iterDirDeriv vs φ y) w]
    simp only [add_sub_cancel_right]
  have e2 : ∫ y, g (y - w) * φ y = ∫ x, g x * φ (x + w) := by
    rw [← integral_add_right_eq_self (fun y => g (y - w) * φ y) w]
    simp only [add_sub_cancel_right]
  rw [e1, e2, h _ (isTestFn_comp_add_right hφ w)]

/-- The integrand `f(y - w) K_i(w) ψ(y)` of the pairing `∫ Kf ψ` is integrable on the product,
for `f ∈ L¹` and continuous compactly supported `ψ` (near part: `K_near ∈ L¹`, `ψ` bounded; far
part: `K_far` bounded, `ψ ∈ L¹`). -/
theorem integrable_pairing_integrand {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2)
    {ψ : ℂ → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p : ℂ × ℂ => f (p.1 - p.2) * kernel i p.2 * ψ p.1)
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψc
  have hn : Integrable (fun p : ℂ × ℂ => nearKernel i p.2 * f (p.1 - p.2) * ψ p.1)
      (volume.prod volume) :=
    ((integrable_nearKernel i).convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf).mul_bdd
      (hψ.comp continuous_fst).aestronglyMeasurable (ae_of_all _ fun p => hC p.1)
  have hrefl : Integrable (fun z => f (-z)) volume := hf.comp_neg
  have hψi : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hψc
  have hf0 : Integrable (fun p : ℂ × ℂ => ψ p.2 * f (-(p.1 - p.2))) (volume.prod volume) :=
    hψi.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hrefl
  have hf1 : Integrable (fun p : ℂ × ℂ => farKernel i p.2 * (ψ p.1 * f (-(p.2 - p.1))))
      (volume.prod volume) :=
    hf0.swap.bdd_mul ((measurable_farKernel i).comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun p => norm_farKernel_le i p.2)
  refine (hn.add hf1).congr (ae_of_all _ fun p => ?_)
  have hk : kernel i p.2 = nearKernel i p.2 + farKernel i p.2 := by
    rw [← nearKernel_add_farKernel i, Pi.add_apply]
  simp only [Pi.add_apply, neg_sub]
  rw [hk]
  ring

/-- **The pairing identity** `∫ (Kf) ψ = ∫ K_i(w) (∫ f(y - w) ψ(y) dy) dw` (Fubini). -/
theorem integral_biotSavart_mul {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2)
    {ψ : ℂ → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, biotSavart f i y * ψ y = ∫ w, kernel i w * ∫ y, f (y - w) * ψ y := by
  have hG := integrable_pairing_integrand hf i hψ hψc
  have e1 : ∀ y, biotSavart f i y * ψ y = ∫ w, f (y - w) * kernel i w * ψ y := by
    intro y
    rw [biotSavart, convolution_eq_swap, ← integral_mul_const]
    rfl
  simp_rw [e1]
  rw [integral_integral_swap (f := fun y w => f (y - w) * kernel i w * ψ y) hG]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  ring

/-- **`∂^{vs} (Kf) = K (∂^{vs} f)` weakly** (tex 1208–1210): if `f, g ∈ L¹` and `g = ∂_{vs} f`
weakly on the plane, then `Kg = ∂_{vs}(Kf)` weakly, componentwise. -/
theorem hasWeakDerivOn_biotSavart {vs : List ℂ} {f g : ℂ → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (h : HasWeakDerivOn univ vs f g) (i : Fin 2) :
    HasWeakDerivOn univ vs (biotSavart f i) (biotSavart g i) := by
  intro φ hφ
  have hD := hφ.iterDirDeriv vs
  rw [integral_biotSavart_mul hf i hD.continuous hD.compact,
    integral_biotSavart_mul hg i hφ.continuous hφ.compact]
  simp_rw [integral_translate_weakDeriv h hφ]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only
  ring

/-! ### The first-order `L²` bound (named hypothesis) -/

/-- The two coordinate directions `∂₁ = ∂_1`, `∂₂ = ∂_I` (as in `pdList`). -/
def dir : Fin 2 → ℂ
  | 0 => 1
  | 1 => Complex.I

/-- **The first-order `L²` bound, as a proposition** (Plancherel / Calderón–Zygmund). The base case
`|α| = 1` of the manuscript's multiplier statement (`paper/main.tex:1208–1210`, B0059; blueprint
infrastructure INF21 "Plancherel and L² Fourier multipliers"): there is a constant `C ≥ 0` such
that for every complex `g ∈ L¹ ∩ L²(ℝ²)` and all `i, k`, the component `(Kg)_i` has a weak
derivative `∂_k (Kg)_i ∈ L²` with `‖∂_k (Kg)_i‖₂ ≤ C ‖g‖₂`. (The multiplier of `∂_k K_i` is
`ξ_k (iξ^⊥)_i / |ξ|²`, of modulus `≤ 1`, so the statement holds with `C = 1`; the
NonUniqueEuler reference proves `‖∇(K ⋆ ω)‖₂ = ‖ω‖₂` for real `ω ∈ L¹ ∩ L²` in
`NonUniqueEuler/lean/NonUniqueEuler/P/Sec2/Velocity.lean:223`, `gradL2_velocity`; its import
closure is reused from `Lib/Kernels/PlanarBS/`, the modules not vendored there are transported to
`Units/B0059/NUE/`, and `Units/B0059/GradL2.lean` proves `GradL2Bound 2`.) -/
def GradL2Bound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ g : ℂ → ℂ, Integrable g volume → MemLp g 2 volume → ∀ i k : Fin 2,
    ∃ h : ℂ → ℂ, MemLp h 2 volume ∧ HasWeakDerivOn univ [dir k] (biotSavart g i) h ∧
      eLpNorm h 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 volume

/-- Every multi-index of positive order is `e_k + β`, with `pdList α = [∂_k] ++ pdList β`. -/
theorem exists_lower {α : ℕ × ℕ} (h : 1 ≤ α.1 + α.2) :
    ∃ (k : Fin 2) (β : ℕ × ℕ), β.1 + β.2 + 1 = α.1 + α.2 ∧ pdList α = [dir k] ++ pdList β := by
  obtain ⟨a, b⟩ := α
  cases a with
  | zero =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by simp at h; omega⟩
    refine ⟨1, (0, b'), by simp, ?_⟩
    simp [pdList, List.replicate_succ, dir]
  | succ a =>
    refine ⟨0, (a, b), by simp; omega, ?_⟩
    simp [pdList, List.replicate_succ, dir]

/-! ### Derivative bounds of positive order (tex 1208–1210) -/

section Bounds

variable {j : ℕ} {M C : ℝ}

/-- **`∂^α (Kf) ∈ L²` for `1 ≤ |α| ≤ j + 1`** (tex 1208–1210): for `f ∈ H^j_M`, `M > 1`, the weak
derivative `∂^α (Kf)_i` exists in `L²` and `‖∂^α (Kf)_i‖₂ ≤ C ‖∂^β f‖₂` where `α = e_k + β`,
`|β| = |α| - 1` (conditional on `GradL2Bound C`). -/
theorem exists_weakDeriv_biotSavart (hCZ : GradL2Bound C) (hM : 1 < M) (F : B0008.HjM j M)
    (i : Fin 2) {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ j + 1) (hα1 : 1 ≤ α.1 + α.2) :
    ∃ g : ℂ → ℂ, MemLp g 2 volume ∧ HasWeakDerivOn univ (pdList α) (biotSavart F.value i) g ∧
      ∃ β : Idx j, β.1.1 + β.1.2 + 1 = α.1 + α.2 ∧
        eLpNorm g 2 volume ≤ ENNReal.ofReal C * eLpNorm (F.der β : ℂ → ℂ) 2 volume := by
  obtain ⟨k, β, hβ, hpd⟩ := exists_lower hα1
  have hβm : β ∈ multiIdx j := mem_multiIdx.2 (by omega)
  set β' : Idx j := ⟨β, hβm⟩
  have hM0 : 0 ≤ M := by linarith
  have hu1 : Integrable (F.der β' : ℂ → ℂ) volume := integrable_L2w hM _
  have hu2 : MemLp (F.der β' : ℂ → ℂ) 2 volume := HjM.memLp_der_volume hM0 F β'
  obtain ⟨g, hg2, hgd, hgb⟩ := hCZ.2 _ hu1 hu2 i k
  have hcomm : HasWeakDerivOn univ (pdList β) (biotSavart F.value i)
      (biotSavart (F.der β') i) :=
    hasWeakDerivOn_biotSavart (B0008.HjM.integrable_value hM F) hu1 (F.hasWeakDeriv β') i
  refine ⟨g, hg2, ?_, β', hβ, hgb⟩
  rw [hpd]
  exact hcomm.trans hgd

/-- **`‖∂^α Kf‖₂ ≤ C_α ‖f‖_{H^{|α|-1}}` for `|α| ≥ 1`** (`paper/main.tex:1210`, the first estimate
of `eq:st18-t00048`, B0059), for `f ∈ H^j_M`, `M > 1`, `1 ≤ |α| ≤ j + 1`, with `C_α = C` from
`GradL2Bound C`. Here `∂^α Kf` is the (chosen) weak derivative `weakPartial α`, which is shown to
be a weak derivative (so the junk value `0` is excluded), and
`‖f‖_{H^{|α|-1}}` is the unweighted Sobolev norm `normH (|α| - 1) f` (meaningful: `memH_value`). -/
theorem l2_weakPartial_biotSavart_le_of_gradL2Bound (hCZ : GradL2Bound C) (hM : 1 < M)
    (F : B0008.HjM j M) (i : Fin 2) {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ j + 1)
    (hα1 : 1 ≤ α.1 + α.2) :
    HasWeakDerivOn univ (pdList α) (biotSavart F.value i)
        (weakPartial α (biotSavart F.value i)) ∧
      MemLp (weakPartial α (biotSavart F.value i)) 2 volume ∧
      l2 (weakPartial α (biotSavart F.value i)) ≤
        C * normH (α.1 + α.2 - 1) (F.value : ℂ → ℂ) := by
  obtain ⟨g, hg2, hgd, β, hβ, hgb⟩ := exists_weakDeriv_biotSavart hCZ hM F i hα hα1
  have hgl := (hg2.locallyIntegrable one_le_two).locallyIntegrableOn univ
  have h := weakDerivOn_ae_eq isOpen_univ hgl hgd
  have hae : weakPartial α (biotSavart F.value i) =ᵐ[volume] g := by
    filter_upwards [h] with x hx using hx (mem_univ x)
  refine ⟨(weakDerivOn_spec hgl hgd).2, hg2.ae_eq hae.symm, ?_⟩
  have hM0 : 0 ≤ M := by linarith
  have hfin : eLpNorm (F.der β : ℂ → ℂ) 2 volume ≠ ⊤ :=
    (HjM.memLp_der_volume hM0 F β).2.ne
  have hβm : β.1 ∈ multiIdx (α.1 + α.2 - 1) := mem_multiIdx.2 (by omega)
  calc l2 (weakPartial α (biotSavart F.value i)) = (eLpNorm g 2 volume).toReal := by
        rw [l2, eLpNorm_congr_ae hae]
    _ ≤ (ENNReal.ofReal C * eLpNorm (F.der β : ℂ → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hgb
    _ = C * l2 (weakPartial β.1 (F.value : ℂ → ℂ)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCZ.1, HjM.l2_weakPartial_value]
    _ ≤ C * normH (α.1 + α.2 - 1) (F.value : ℂ → ℂ) :=
        mul_le_mul_of_nonneg_left (l2_weakPartial_le_normH hβm _) hCZ.1

end Bounds

/-! ### The local bound `‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}` (tex 1211) -/

/-- `‖K_near,0‖₁ + ‖K_near,1‖₁`, a bound for each near kernel's `L¹` norm. -/
def nearL1 : ℝ≥0∞ := ∑ i : Fin 2, ∫⁻ z, ‖nearKernel i z‖ₑ

theorem nearL1_ne_top : nearL1 ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun i _ => (integrable_nearKernel i).2.ne

theorem lintegral_nearKernel_le (i : Fin 2) : ∫⁻ z, ‖nearKernel i z‖ₑ ≤ nearL1 :=
  Finset.single_le_sum (f := fun i => ∫⁻ z, ‖nearKernel i z‖ₑ) (fun _ _ => zero_le)
    (Finset.mem_univ i)

/-- The constant `‖K_near‖₁ + |B_R|^{1/2} π⁻¹ C_M` of the `L²(B_R)` bound of `Kf` on `H^j_M`. -/
def ballConst (M R : ℝ) : ℝ :=
  nearL1.toReal +
    (volume (ball (0 : ℂ) R) ^ (2 : ℝ≥0∞).toReal⁻¹).toReal * (Real.pi⁻¹ * CM M)

section Local

variable {j : ℕ} {M C : ℝ}

/-- `‖Kf‖_{L²(B_R)} ≤ (‖K_near‖₁ + |B_R|^{1/2} π⁻¹ C_M) ‖f‖_{H^j_M}` for `f ∈ H^j_M`, `M > 1`
(the order-zero part of tex 1211; no global weighted velocity bound is claimed). -/
theorem eLpNorm_biotSavart_ball_le_HjM (hM : 1 < M) (F : B0008.HjM j M) (i : Fin 2) (R : ℝ) :
    eLpNorm (biotSavart F.value i) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      ENNReal.ofReal (ballConst M R * ‖F‖) := by
  have hM0 : 0 ≤ M := by linarith
  have hf1 := B0008.HjM.integrable_value hM F
  have hf2 : MemLp (F.value : ℂ → ℂ) 2 volume := HjM.memLp_der_volume hM0 F (idx0 j)
  have h := eLpNorm_biotSavart_ball_le hf1 hf2 i R
  set V := volume (ball (0 : ℂ) R) ^ (2 : ℝ≥0∞).toReal⁻¹ with hVdef
  have hV : V ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) measure_ball_lt_top.ne
  have hCM : 0 ≤ CM M := Real.sqrt_nonneg _
  have hpi : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  have h1 : (∫⁻ z, ‖nearKernel i z‖ₑ) * eLpNorm (F.value : ℂ → ℂ) 2 volume ≤
      ENNReal.ofReal (nearL1.toReal * ‖F‖) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal nearL1_ne_top]
    exact mul_le_mul' (lintegral_nearKernel_le i) (HjM.eLpNorm_der_le hM0 F (idx0 j))
  have h2 : V * ENNReal.ofReal (Real.pi⁻¹ * ∫ t, ‖F.value t‖) ≤
      ENNReal.ofReal (V.toReal * (Real.pi⁻¹ * CM M * ‖F‖)) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (integral_norm_value_le hM F) hpi
  refine h.trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))
    (mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (mul_nonneg hpi hCM) (norm_nonneg _)))]
  congr 1
  rw [ballConst, ← hVdef]
  ring

/-- **`‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`** (`paper/main.tex:1211`, the second
estimate of `eq:st18-t00048`, B0059): for `M > 1`, every `j` and every radius `R` there is a
constant `C_{j,M,R} ≥ 0` (depending also on the constant of `GradL2Bound C`) such that for every
`f ∈ H^j_M` and each component `i`, `(Kf)_i ∈ H^{j+1}(B_R)` and
`‖(Kf)_i‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`. The norm is the manuscript's sum of squares
of the `L²(B_R)` norms of all weak derivatives of order `≤ j + 1` on `B_R` (`normHOn`). -/
theorem memHOn_biotSavart_ball_of_gradL2Bound (hCZ : GradL2Bound C) (hM : 1 < M) (j : ℕ) (R : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (F : B0008.HjM j M) (i : Fin 2),
      MemHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ∧
        normHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ≤ C' * ‖F‖ := by
  set c := max (ballConst M R) C with hcdef
  have hc : 0 ≤ c := le_max_of_le_right hCZ.1
  refine ⟨Real.sqrt (multiIdx (j + 1)).card * c, mul_nonneg (Real.sqrt_nonneg _) hc,
    fun F i => ?_⟩
  set B := ball (0 : ℂ) R with hBdef
  set u := biotSavart (F.value : ℂ → ℂ) i with hudef
  have hM0 : 0 ≤ M := by linarith
  have hf1 := B0008.HjM.integrable_value hM F
  have hf2 : MemLp (F.value : ℂ → ℂ) 2 volume := HjM.memLp_der_volume hM0 F (idx0 j)
  have hloc : LocallyIntegrable u volume := locallyIntegrable_biotSavart hf1 hf2 i
  have h0 := eLpNorm_biotSavart_ball_le_HjM hM F i R
  have hmem0 : MemLp u 2 (volume.restrict B) :=
    ⟨(aestronglyMeasurable_biotSavart hf1.aestronglyMeasurable i).restrict,
      h0.trans_lt ENNReal.ofReal_lt_top⟩
  have key : ∀ γ ∈ multiIdx (j + 1), ∃ g : ℂ → ℂ, MemLp g 2 (volume.restrict B) ∧
      LocallyIntegrableOn g B ∧ HasWeakDerivOn B (pdList γ) u g ∧
      eLpNorm g 2 (volume.restrict B) ≤ ENNReal.ofReal (c * ‖F‖) := by
    intro γ hγ
    by_cases hγ0 : γ.1 + γ.2 = 0
    · have hγe : pdList γ = [] := by
        obtain ⟨a, b⟩ := γ
        obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by simp only at hγ0; omega
        simp [pdList]
      refine ⟨u, hmem0, hloc.locallyIntegrableOn B, ?_, h0.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      · rw [hγe]
        intro φ _
        simp
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · have hγ1 : 1 ≤ γ.1 + γ.2 := Nat.one_le_iff_ne_zero.2 hγ0
      obtain ⟨g, hg2, hgd, β, -, hgb⟩ :=
        exists_weakDeriv_biotSavart hCZ hM F i (mem_multiIdx.1 hγ) hγ1
      refine ⟨g, hg2.restrict B, (hg2.locallyIntegrable one_le_two).locallyIntegrableOn B,
        hgd.mono (subset_univ _), ?_⟩
      calc eLpNorm g 2 (volume.restrict B) ≤ eLpNorm g 2 volume := eLpNorm_restrict_le _ _ _ _
        _ ≤ ENNReal.ofReal C * eLpNorm (F.der β : ℂ → ℂ) 2 volume := hgb
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖F‖ :=
            mul_le_mul' le_rfl (HjM.eLpNorm_der_le hM0 F β)
        _ = ENNReal.ofReal (C * ‖F‖) := (ENNReal.ofReal_mul hCZ.1).symm
        _ ≤ ENNReal.ofReal (c * ‖F‖) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  choose! G hG2 hGloc hGd hGb using key
  refine ⟨⟨hmem0, fun γ hγ => ⟨G γ, hG2 γ hγ, hGd γ hγ⟩⟩, ?_⟩
  have hterm : ∀ γ ∈ multiIdx (j + 1), l2On B (weakPartialOn B γ u) ≤ c * ‖F‖ := by
    intro γ hγ
    have h := weakDerivOn_ae_eq isOpen_ball (hGloc γ hγ) (hGd γ hγ)
    have hae : weakPartialOn B γ u =ᵐ[volume.restrict B] G γ :=
      (ae_restrict_iff' measurableSet_ball).2 h
    rw [l2On, eLpNorm_congr_ae hae]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc (norm_nonneg _)) (hGb γ hγ)
  rw [normHOn]
  calc Real.sqrt (∑ γ ∈ multiIdx (j + 1), l2On B (weakPartialOn B γ u) ^ 2)
      ≤ Real.sqrt (∑ γ ∈ multiIdx (j + 1), (c * ‖F‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun γ hγ =>
          pow_le_pow_left₀ (l2On_nonneg _ _) (hterm γ hγ) 2)
    _ = Real.sqrt (multiIdx (j + 1)).card * c * ‖F‖ := by
        rw [Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
          Real.sqrt_sq (mul_nonneg hc (norm_nonneg _))]
        ring

end Local

/-! ### The unit, assembled -/

/-- **B0059** (`paper/main.tex:1206–1213`, `eq:st18-t00048`), conditional on the named
Plancherel/Calderón–Zygmund hypothesis `GradL2Bound C` (first-order case of the multiplier
sentence, tex 1208–1209). For `M > 1` and every `j`:
1. `‖f‖₁ ≤ C_M ‖f‖_{L²_M}` on `H^j_M`;
2. the smooth split `K = K_near + K_far` at distance one: `K_near ∈ L¹` maps `L²` to `L²`
   (Young), `K_far` is bounded (by `1/π`) and maps `L¹` to `L^∞`, and `Kf = f ⋆ K_near + f ⋆ K_far`
   a.e. for `f ∈ L¹`;
3. `‖∂^α Kf‖₂ ≤ C ‖f‖_{H^{|α|-1}}` for `1 ≤ |α| ≤ j + 1`;
4. for every `R`, `‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`.
No global weighted velocity estimate is asserted (tex 1213). -/
theorem unit_statement_of_gradL2Bound {C : ℝ} (hCZ : GradL2Bound C) {M : ℝ} (hM : 1 < M) (j : ℕ) :
    (∀ F : B0008.HjM j M, ∫ y, ‖F.value y‖ ≤ CM M * ‖F‖) ∧
    (∀ i : Fin 2, nearKernel i + farKernel i = kernel i ∧ Integrable (nearKernel i) volume ∧
      (∀ z, ‖farKernel i z‖ ≤ Real.pi⁻¹) ∧
      (∀ f : ℂ → ℂ, MemLp f 2 volume → MemLp (nearPart f i) 2 volume ∧
        eLpNorm (nearPart f i) 2 volume ≤ (∫⁻ z, ‖nearKernel i z‖ₑ) * eLpNorm f 2 volume) ∧
      (∀ f : ℂ → ℂ, Integrable f volume →
        (∀ y, ‖farPart f i y‖ ≤ Real.pi⁻¹ * ∫ t, ‖f t‖) ∧
        biotSavart f i =ᵐ[volume] nearPart f i + farPart f i)) ∧
    (∀ (F : B0008.HjM j M) (i : Fin 2) (α : ℕ × ℕ), α.1 + α.2 ≤ j + 1 → 1 ≤ α.1 + α.2 →
      HasWeakDerivOn univ (pdList α) (biotSavart F.value i)
          (weakPartial α (biotSavart F.value i)) ∧
        MemLp (weakPartial α (biotSavart F.value i)) 2 volume ∧
        l2 (weakPartial α (biotSavart F.value i)) ≤
          C * normH (α.1 + α.2 - 1) (F.value : ℂ → ℂ)) ∧
    (∀ R : ℝ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (F : B0008.HjM j M) (i : Fin 2),
      MemHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ∧
        normHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ≤ C' * ‖F‖) :=
  ⟨fun F => integral_norm_value_le hM F,
    fun i => ⟨nearKernel_add_farKernel i, integrable_nearKernel i, norm_farKernel_le i,
      fun _ hf => memLp_nearPart hf i,
      fun _ hf => ⟨norm_farPart_le hf i, biotSavart_ae_eq_near_add_far hf i⟩⟩,
    fun F i _ hα hα1 => l2_weakPartial_biotSavart_le_of_gradL2Bound hCZ hM F i hα hα1,
    fun R => memHOn_biotSavart_ball_of_gradL2Bound hCZ hM j R⟩

end UnforcedLeray.B0059
