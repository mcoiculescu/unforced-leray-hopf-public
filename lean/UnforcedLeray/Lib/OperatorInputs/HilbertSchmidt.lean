import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import UnforcedLeray.Infra.WeaklyNullCompact
import UnforcedLeray.Infra.FiniteRankApprox

/-!
# Integral operators with square-integrable kernels (ExternalInputs E3, `STD:hilbert-schmidt`)


bypass BX11; Wave 1 block 1G part 4. Blueprint units **B0069** (`paper/main.tex` 1281–1293:
"Since `∫ r v(r) dr < ∞`, this is Hilbert–Schmidt", used for the compactness of `𝒦_n`) and
**B0759** (`paper/main.tex` 10340–10368: the operator norm of an integral operator is at most the
`L²` norm of its kernel).

Let `(α, μ)` and `(β, ν)` be s-finite measure spaces and `k ∈ L²(μ ⊗ ν)` a complex kernel. Then

* `exists_integralOperator`: there is a bounded operator `T : L²(ν) → L²(μ)` with
  `(T f)(x) = ∫ k(x, y) f(y) dν(y)` for `μ`-a.e. `x`, `‖T‖ ≤ ‖k‖_{L²(μ⊗ν)}`, and `T` is compact.
  The norm bound is the Cauchy–Schwarz/Tonelli argument of B0759; compactness is the
  Hilbert–Schmidt property of B0069.
* `exists_integralOperator_norm_le`: the statement of scoping note §5.2 E3 (operator and norm
  bound), and `isCompactOperator_of_memLp_kernel`: every operator given a.e. by an `L²` kernel is
  compact.

The integral `∫ k(x, y) f(y) dν(y)` is Mathlib's Bochner integral, which is `0` when the integrand
is not integrable. This junk value is harmless: for `μ`-a.e. `x` the section `k(x, ·)` is in
`L²(ν)` (`ae_memLp_section`), so the integrand is integrable, and the conclusion is only an a.e.
identity.

**Proof of compactness.** Instead of a Hilbert–Schmidt class (absent from Mathlib) we use the
weakly-null criterion of the WIP module `UnforcedLeray.Infra.WeaklyNullCompact`
(`isCompactOperator_of_forall_weaklyNull_of_norm_le_one`). For a weakly null sequence `fₙ` in
the unit ball, `(T fₙ)(x) = ⟪conj k(x, ·), fₙ⟫ → 0` for a.e. `x` and
`|(T fₙ)(x)|² ≤ ‖k(x, ·)‖²`, whose integral is `‖k‖²_{L²(μ⊗ν)} < ∞` by Tonelli; dominated
convergence gives `‖T fₙ‖ → 0`. With the WIP module `UnforcedLeray.Infra.FiniteRankApprox`,
`kernelOperator_mem_approximable` then exhibits `T` as an operator-norm limit of finite-rank
operators.

No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.ExternalInputs

/-- `‖f‖_{L²}² = ∫ ‖f‖²` in `ℝ≥0∞` (real exponent `2`). -/
theorem eLpNorm_two_rpow_two {γ E : Type*} [MeasurableSpace γ] {m : Measure γ}
    [NormedAddCommGroup E] (f : γ → E) :
    eLpNorm f 2 m ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂m := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := m) (f := f) (p := 2) two_ne_zero
  simpa using h

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

section Sections

variable [SFinite ν]

/-- Tonelli for the squared kernel: `∫ ‖k(x, ·)‖²_{L²(ν)} dμ(x) = ‖k‖²_{L²(μ⊗ν)}`. -/
theorem lintegral_eLpNorm_section_sq {k : α × β → ℂ} (hk : AEStronglyMeasurable k (μ.prod ν)) :
    ∫⁻ x, eLpNorm (fun y => k (x, y)) 2 ν ^ (2 : ℝ) ∂μ = eLpNorm k 2 (μ.prod ν) ^ (2 : ℝ) := by
  rw [eLpNorm_two_rpow_two k, lintegral_prod _ (hk.enorm.pow_const _)]
  refine lintegral_congr fun x => ?_
  rw [eLpNorm_two_rpow_two]

/-- For `μ`-a.e. `x` the section `y ↦ k (x, y)` of an `L²(μ ⊗ ν)` kernel lies in `L²(ν)`. -/
theorem ae_memLp_section {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 ν := by
  have hfin : ∫⁻ x, eLpNorm (fun y => k (x, y)) 2 ν ^ (2 : ℝ) ∂μ ≠ ∞ := by
    rw [lintegral_eLpNorm_section_sq hk.1]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hk.2.ne).ne
  have hmeas : AEMeasurable (fun x => eLpNorm (fun y => k (x, y)) 2 ν ^ (2 : ℝ)) μ := by
    have h := (hk.1.enorm.pow_const (2 : ℝ)).lintegral_prod_right'
    refine h.congr (Eventually.of_forall fun x => ?_)
    exact (eLpNorm_two_rpow_two _).symm
  filter_upwards [hk.1.prodMk_left, ae_lt_top' hmeas hfin] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact (ENNReal.rpow_lt_top_iff_of_pos h2).mp hx2

end Sections

/-- On a good section, the kernel integral is an `L²` inner product:
`∫ k(x, y) f(y) dν(y) = ⟪conj k(x, ·), f⟫`. -/
theorem integral_section_mul_eq_inner {k : β → ℂ} (hk : MemLp k 2 ν) (f : Lp ℂ 2 ν) :
    ∫ y, k y * f y ∂ν = ⟪hk.star.toLp (star k), f⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hk.star.coeFn_toLp] with y hy
  rw [hy, RCLike.inner_apply']
  simp

/-- Cauchy–Schwarz on a good section: `‖∫ k f dν‖ ≤ ‖k‖_{L²} ‖f‖_{L²}`. -/
theorem norm_integral_section_mul_le {k : β → ℂ} (hk : MemLp k 2 ν) (f : Lp ℂ 2 ν) :
    ‖∫ y, k y * f y ∂ν‖ ≤ (eLpNorm k 2 ν).toReal * ‖f‖ := by
  rw [integral_section_mul_eq_inner hk f]
  refine (norm_inner_le_norm _ _).trans_eq ?_
  rw [Lp.norm_toLp, eLpNorm_star]

section Operator

variable [SFinite ν]

/-- The function `x ↦ ∫ k(x, y) f(y) dν(y)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_kernelIntegral {k : α × β → ℂ}
    (hk : AEStronglyMeasurable k (μ.prod ν)) (f : Lp ℂ 2 ν) :
    AEStronglyMeasurable (fun x => ∫ y, k (x, y) * f y ∂ν) μ := by
  have hf : AEStronglyMeasurable (fun z : α × β => (f : β → ℂ) z.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable f).comp_snd
  exact (hk.mul hf).integral_prod_right'

/-- The pointwise Hilbert–Schmidt bound `‖(T f)(x)‖ₑ ≤ ‖k(x, ·)‖_{L²(ν)} ‖f‖ₑ`, for a.e. `x`. -/
theorem ae_enorm_kernelIntegral_le {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ∀ᵐ x ∂μ, ‖∫ y, k (x, y) * f y ∂ν‖ₑ ≤ eLpNorm (fun y => k (x, y)) 2 ν * ‖f‖ₑ := by
  filter_upwards [ae_memLp_section hk] with x hx
  have h := norm_integral_section_mul_le hx f
  rw [← ofReal_norm, ← ofReal_norm]
  calc ENNReal.ofReal ‖∫ y, k (x, y) * f y ∂ν‖
      ≤ ENNReal.ofReal ((eLpNorm (fun y => k (x, y)) 2 ν).toReal * ‖f‖) :=
        ENNReal.ofReal_le_ofReal h
    _ = eLpNorm (fun y => k (x, y)) 2 ν * ENNReal.ofReal ‖f‖ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.2.ne]

/-- The `L²` bound `‖T f‖_{L²(μ)} ≤ ‖k‖_{L²(μ⊗ν)} ‖f‖_{L²(ν)}` (B0759, Cauchy–Schwarz and
Tonelli), in `ℝ≥0∞`. -/
theorem eLpNorm_kernelIntegral_le {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    eLpNorm (fun x => ∫ y, k (x, y) * f y ∂ν) 2 μ ≤ eLpNorm k 2 (μ.prod ν) * ‖f‖ₑ := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [← ENNReal.rpow_le_rpow_iff h2, eLpNorm_two_rpow_two, ENNReal.mul_rpow_of_nonneg _ _ h2.le,
    ← lintegral_eLpNorm_section_sq hk.1, ← lintegral_mul_const' _ _
      (ENNReal.rpow_ne_top_of_nonneg h2.le enorm_ne_top)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_enorm_kernelIntegral_le hk f] with x hx
  rw [← ENNReal.mul_rpow_of_nonneg _ _ h2.le]
  exact ENNReal.rpow_le_rpow hx h2.le

theorem memLp_kernelIntegral {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    MemLp (fun x => ∫ y, k (x, y) * f y ∂ν) 2 μ :=
  ⟨aestronglyMeasurable_kernelIntegral hk.1 f,
    (eLpNorm_kernelIntegral_le hk f).trans_lt (ENNReal.mul_lt_top hk.2 enorm_lt_top)⟩

/-- On the full-measure set of good sections the kernel integral is the inner product with
`conj k(x, ·)`; in particular it is linear in `f` there. -/
theorem ae_kernelIntegral_eq_inner {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∃ K : Lp ℂ 2 ν, ‖K‖ = (eLpNorm (fun y => k (x, y)) 2 ν).toReal ∧
      ∀ f : Lp ℂ 2 ν, ∫ y, k (x, y) * f y ∂ν = ⟪K, f⟫_ℂ := by
  filter_upwards [ae_memLp_section hk] with x hx
  refine ⟨hx.star.toLp _, ?_, fun f => integral_section_mul_eq_inner hx f⟩
  rw [Lp.norm_toLp, eLpNorm_star]

/-- The integral operator of an `L²(μ ⊗ ν)` kernel, as a linear map `L²(ν) → L²(μ)`. -/
def kernelOperatorₗ {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_kernelIntegral hk f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_kernelIntegral_eq_inner hk] with x hx
    obtain ⟨K, -, hK⟩ := hx
    simp only [Pi.add_apply, hK, inner_add_right]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_kernelIntegral_eq_inner hk] with x hx
    obtain ⟨K, -, hK⟩ := hx
    simp only [Pi.smul_apply, hK, inner_smul_right, smul_eq_mul]

theorem coeFn_kernelOperatorₗ {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    (kernelOperatorₗ hk f : α → ℂ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  (memLp_kernelIntegral hk f).coeFn_toLp

theorem norm_kernelOperatorₗ_le {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    ‖kernelOperatorₗ hk f‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal * ‖f‖ := by
  change ‖(memLp_kernelIntegral hk f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, ← toReal_enorm f, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hk.2.ne enorm_ne_top)
    (eLpNorm_kernelIntegral_le hk f)

/-- **The integral operator of an `L²` kernel** (B0069, B0759): the bounded operator
`L²(ν) → L²(μ)`, `f ↦ ∫ k(·, y) f(y) dν(y)`. -/
def kernelOperator {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (kernelOperatorₗ hk).mkContinuous _ (norm_kernelOperatorₗ_le hk)

theorem coeFn_kernelOperator {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    (kernelOperator hk f : α → ℂ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  coeFn_kernelOperatorₗ hk f

/-- **Operator norm at most the `L²` norm of the kernel** (B0759, `paper/main.tex` 10363–10366). -/
theorem norm_kernelOperator_le {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ‖kernelOperator hk‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- **Hilbert–Schmidt operators are compact** (B0069, `paper/main.tex` 1291–1293). The
integral operator of a kernel `k ∈ L²(μ ⊗ ν)` is a compact operator `L²(ν) → L²(μ)`. -/
theorem isCompactOperator_kernelOperator {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    IsCompactOperator (kernelOperator hk) := by
  refine Infra.WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull_of_norm_le_one _ ?_
  intro u hu hweak
  have h2 : (0 : ℝ) < 2 := by norm_num
  -- the squared `L²` norms tend to `0` by dominated convergence
  have hlim : Tendsto (fun n => ∫⁻ x, ‖∫ y, k (x, y) * u n y ∂ν‖ₑ ^ (2 : ℝ) ∂μ) atTop
      (𝓝 (∫⁻ _x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence'
      (fun x => eLpNorm (fun y => k (x, y)) 2 ν ^ (2 : ℝ))
      (fun n => (aestronglyMeasurable_kernelIntegral hk.1 (u n)).enorm.pow_const _) ?_ ?_ ?_
    · intro n
      filter_upwards [ae_enorm_kernelIntegral_le hk (u n)] with x hx
      refine ENNReal.rpow_le_rpow (hx.trans ?_) h2.le
      calc eLpNorm (fun y => k (x, y)) 2 ν * ‖u n‖ₑ
          ≤ eLpNorm (fun y => k (x, y)) 2 ν * 1 := by
            gcongr
            rw [← ofReal_norm, ENNReal.ofReal_le_one]
            exact hu n
        _ = _ := mul_one _
    · rw [lintegral_eLpNorm_section_sq hk.1]
      exact (ENNReal.rpow_lt_top_of_nonneg h2.le hk.2.ne).ne
    · filter_upwards [ae_kernelIntegral_eq_inner hk] with x hx
      obtain ⟨K, -, hK⟩ := hx
      simp_rw [hK]
      have h0 : Tendsto (fun n => ⟪K, u n⟫_ℂ) atTop (𝓝 0) := hweak K
      have h1 : Tendsto (fun n => ‖⟪K, u n⟫_ℂ‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : ℂ)).comp h0
        rw [enorm_zero] at this
        exact this
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h1
      rw [ENNReal.zero_rpow_of_pos h2] at h3
      exact h3
  rw [lintegral_zero] at hlim
  -- back to the operator norms
  have hnorm : ∀ n, ‖kernelOperator hk (u n)‖ =
      ((∫⁻ x, ‖∫ y, k (x, y) * u n y ∂ν‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))).toReal := by
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_kernelOperator hk (u n)),
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  simp_rw [hnorm]
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h4
  have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h4
  rw [ENNReal.toReal_zero] at h5
  exact h5

/-- The integral operator of an `L²` kernel is an operator-norm limit of finite-rank operators
(through `Infra.FiniteRankApprox.mem_approximable_of_isCompactOperator`). -/
theorem kernelOperator_mem_approximable {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    kernelOperator hk ∈ Infra.FiniteRankApprox.approximable ℂ (Lp ℂ 2 ν) (Lp ℂ 2 μ) :=
  Infra.FiniteRankApprox.mem_approximable_of_isCompactOperator
    (isCompactOperator_kernelOperator hk)

/-- **E3** (scoping note §5.2): an integral operator with square-integrable kernel exists, is
given a.e. by the kernel integral, has norm at most `‖k‖_{L²(μ⊗ν)}` and is compact. -/
theorem exists_integralOperator {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ,
      (∀ f, (T f : α → ℂ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν) ∧
      ‖T‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal ∧ IsCompactOperator T :=
  ⟨kernelOperator hk, coeFn_kernelOperator hk, norm_kernelOperator_le hk,
    isCompactOperator_kernelOperator hk⟩

/-- **E3**, the form of scoping note §5.2 (operator and norm bound). -/
theorem exists_integralOperator_norm_le {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ,
      (∀ f, (T f : α → ℂ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν) ∧
      ‖T‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal :=
  ⟨kernelOperator hk, coeFn_kernelOperator hk, norm_kernelOperator_le hk⟩

/-- An operator that agrees a.e. with the integral operator of an `L²(μ ⊗ ν)` kernel equals
`kernelOperator`. -/
theorem eq_kernelOperator {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    {T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ}
    (hT : ∀ f, (T f : α → ℂ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν) :
    T = kernelOperator hk := by
  ext1 f
  exact Lp.ext ((hT f).trans (coeFn_kernelOperator hk f).symm)

/-- **Hilbert–Schmidt implies compact** (`STD:hilbert-schmidt`, B0069): any bounded operator
`L²(ν) → L²(μ)` given a.e. by a kernel `k ∈ L²(μ ⊗ ν)` is compact, with norm at most
`‖k‖_{L²(μ⊗ν)}`. -/
theorem isCompactOperator_of_memLp_kernel {k : α × β → ℂ} (hk : MemLp k 2 (μ.prod ν))
    {T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ}
    (hT : ∀ f, (T f : α → ℂ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν) :
    IsCompactOperator T ∧ ‖T‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal := by
  rw [eq_kernelOperator hk hT]
  exact ⟨isCompactOperator_kernelOperator hk, norm_kernelOperator_le hk⟩

end Operator

end UnforcedLeray.ExternalInputs
