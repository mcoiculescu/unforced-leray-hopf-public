import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# B0008: the polynomially weighted Sobolev spaces `H^j_M` and `X_{j,M}` on `ℝ²`

Blueprint unit **B0008**, label `eq:st18-t00003`, `paper/main.tex` lines 653–660.

**Statement.** For an integer `j ≥ 0` and a finite weight exponent `M > 1`,
`H^j_M = {f : ⟨y⟩^M ∂^α f ∈ L²(ℝ²), |α| ≤ j}` (distributional derivatives, complex-valued `f`)
and `X_{j,M} = {f ∈ H^j_M : ∫_{ℝ²} f = 0}`. These are complex Hilbert spaces with the
sum-of-squares norm `‖f‖² = ∑_{|α| ≤ j} ‖⟨y⟩^M ∂^α f‖²_{L²}`, with no angular restriction, and
`M > 1` makes `f ↦ ∫ f` bounded, so `X_{j,M}` is a closed subspace.

**Conventions.**
* The plane `ℝ²` is `ℂ` with Lebesgue measure `volume`; `|y| = ‖y‖`, `⟨y⟩ = (1 + |y|²)^{1/2}`
  (`bracket`). Derivatives `∂^α = ∂₁^{α₁} ∂₂^{α₂}` and the weak-derivative predicate
  `HasWeakDerivOn univ (pdList α)` are those of the vendored, compiled
  `NonUniqueEuler.Defs.Infra.Sobolev` (test functions: smooth, compactly supported, complex).
* `L2w M = L²(⟨y⟩^{2M} dy)` is `MeasureTheory.Lp ℂ 2 (wMeasure M)`, where `wMeasure M` is
  Lebesgue measure with density `(1 + |y|²)^M`. Its norm is `‖⟨y⟩^M f‖_{L²(dy)}` (`norm_L2w`,
  `memLp_wMeasure_iff`). The two measures have the same null sets (`volume_ac`, `wMeasure_ac`).
* `HjM j M` stores `f` together with all its derivatives: it is the closed subspace of
  `PiLp 2 (fun α : Idx j => L2w M)` cut out by the continuous functionals
  `F ↦ ∫ F₀ ∂^α φ - (-1)^{|α|} ∫ F_α φ`. The construction adapts
  `NonUniqueEuler/Defs/Infra/SobolevSpace.lean` of the NonUniqueEuler reference

  from `L²(dy)` to `L²(⟨y⟩^{2M}dy)`: a Lebesgue pairing `∫ F ψ dy` is the weighted inner
  product with `conj ψ / ⟨y⟩^{2M}` (`inner_dualVec`).
* `XjM j M` is the set of `F` with `F.value` Lebesgue integrable and of integral `0`. The
  integrability clause avoids the Bochner junk value `∫ f = 0` for non-integrable `f`; for
  `M > 1` it is automatic (`integrable_L2w`), and `mem_XjM_iff` drops it.

**Main results.** `HjM.completeSpace`, `HjM.norm_sq_eq_weighted`, `HjM.inner_eq`,
`mem_HSub_iff`, `memHjM_iff` (the Hilbert space realizes exactly the function-level
membership `MemHjM`), `HjM.ext` (an element is determined by its function), `memHjM_of_testFn`
(non-vacuity), `integrable_inv_weight` (`∫ ⟨y⟩^{-2M} < ∞` for `M > 1`), `norm_integral_le`,
`integral_norm_le` (`‖f‖_{L¹} ≤ C_M ‖⟨y⟩^M f‖_{L²}`, `C_M = (∫ ⟨y⟩^{-2M})^{1/2}`),
`XjM_eq_ker`, `isClosed_XjM`, `completeSpace_XjM`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff ComplexConjugate

namespace UnforcedLeray.B0008

open NonUniqueEuler.Sob

/-- The Japanese bracket `⟨y⟩ = (1 + |y|²)^{1/2}` on the plane `ℂ = ℝ²`. -/
def bracket (y : ℂ) : ℝ := Real.sqrt (1 + ‖y‖ ^ 2)

theorem one_add_norm_sq_pos (y : ℂ) : 0 < 1 + ‖y‖ ^ 2 := by positivity

theorem bracket_pos (y : ℂ) : 0 < bracket y := Real.sqrt_pos.2 (one_add_norm_sq_pos y)

theorem continuous_bracket : Continuous bracket := by
  unfold bracket
  fun_prop

/-- `⟨y⟩^{2M} = (1 + |y|²)^M`. -/
theorem bracket_rpow_sq (M : ℝ) (y : ℂ) : (bracket y ^ M) ^ 2 = (1 + ‖y‖ ^ 2) ^ M := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (bracket_pos y).le, bracket,
    Real.sqrt_eq_rpow, ← Real.rpow_mul (one_add_norm_sq_pos y).le]
  congr 1
  push_cast
  ring

/-- The weight density `⟨y⟩^{2M} = (1 + |y|²)^M`, as a nonnegative real. -/
def density (M : ℝ) (y : ℂ) : ℝ≥0 := Real.toNNReal ((1 + ‖y‖ ^ 2) ^ M)

theorem coe_density (M : ℝ) (y : ℂ) : (density M y : ℝ) = (1 + ‖y‖ ^ 2) ^ M :=
  Real.coe_toNNReal _ (Real.rpow_nonneg (one_add_norm_sq_pos y).le M)

theorem density_pos (M : ℝ) (y : ℂ) : 0 < (density M y : ℝ) := by
  rw [coe_density]
  exact Real.rpow_pos_of_pos (one_add_norm_sq_pos y) M

theorem continuous_density (M : ℝ) : Continuous (density M) := by
  unfold density
  refine continuous_real_toNNReal.comp ?_
  exact (Continuous.rpow_const (by fun_prop) fun y => Or.inl (one_add_norm_sq_pos y).ne')

theorem measurable_density (M : ℝ) : Measurable (density M) :=
  (continuous_density M).measurable

/-- The weighted measure `⟨y⟩^{2M} dy` on the plane. -/
def wMeasure (M : ℝ) : Measure ℂ := volume.withDensity (fun y => (density M y : ℝ≥0∞))

instance (M : ℝ) : IsLocallyFiniteMeasure (wMeasure M) :=
  IsLocallyFiniteMeasure.withDensity_coe (continuous_density M)

theorem wMeasure_ac (M : ℝ) : wMeasure M ≪ volume :=
  withDensity_absolutelyContinuous _ _

theorem volume_ac (M : ℝ) : (volume : Measure ℂ) ≪ wMeasure M :=
  withDensity_absolutelyContinuous'
    (measurable_density M).coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun y => by
      simpa using (density_pos M y).ne')

/-- The weighted space `L²(⟨y⟩^{2M} dy)` of complex functions on the plane. -/
abbrev L2w (M : ℝ) : Type := Lp ℂ 2 (wMeasure M)

theorem continuous_bracket_rpow (M : ℝ) : Continuous fun y : ℂ => bracket y ^ M :=
  continuous_bracket.rpow_const fun y => Or.inl (bracket_pos y).ne'

theorem continuous_coe_density (M : ℝ) : Continuous fun y : ℂ => (density M y : ℝ) :=
  NNReal.continuous_coe.comp (continuous_density M)

/-- The weighted `L²` seminorm is the `L²` seminorm of `⟨y⟩^M f`. -/
theorem eLpNorm_wMeasure (M : ℝ) (f : ℂ → ℂ) :
    eLpNorm f 2 (wMeasure M) = eLpNorm (fun y => bracket y ^ M • f y) 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), wMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_density M).coe_nnreal_ennreal
      (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply, enorm_smul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [mul_pow, Real.enorm_eq_ofReal (Real.rpow_nonneg (bracket_pos y).le M),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (bracket_pos y).le M), bracket_rpow_sq]
  rfl

theorem aestronglyMeasurable_wMeasure_iff (M : ℝ) {f : ℂ → ℂ} :
    AEStronglyMeasurable f (wMeasure M) ↔
      AEStronglyMeasurable (fun y => bracket y ^ M • f y) volume := by
  constructor
  · intro hf
    exact (continuous_bracket_rpow M).aestronglyMeasurable.smul (hf.mono_ac (volume_ac M))
  · intro hf
    have h2 : AEStronglyMeasurable (fun y => (bracket y ^ M)⁻¹ • (bracket y ^ M • f y)) volume :=
      ((continuous_bracket_rpow M).inv₀ fun y =>
        (Real.rpow_pos_of_pos (bracket_pos y) M).ne').aestronglyMeasurable.smul hf
    have he : (fun y => (bracket y ^ M)⁻¹ • (bracket y ^ M • f y)) = f := by
      funext y
      rw [smul_smul, inv_mul_cancel₀ (Real.rpow_pos_of_pos (bracket_pos y) M).ne', one_smul]
    rw [he] at h2
    exact h2.mono_ac (wMeasure_ac M)

/-- Membership in the weighted space is the manuscript's `⟨y⟩^M f ∈ L²`. -/
theorem memLp_wMeasure_iff (M : ℝ) {f : ℂ → ℂ} :
    MemLp f 2 (wMeasure M) ↔ MemLp (fun y => bracket y ^ M • f y) 2 volume := by
  unfold MemLp
  rw [aestronglyMeasurable_wMeasure_iff, eLpNorm_wMeasure]

/-- The norm of `L²(⟨y⟩^{2M} dy)` is `‖⟨y⟩^M f‖_{L²}`. -/
theorem norm_L2w (M : ℝ) (F : L2w M) :
    ‖F‖ = (eLpNorm (fun y => bracket y ^ M • F y) 2 volume).toReal := by
  rw [Lp.norm_def, eLpNorm_wMeasure]

/-! ### Dual vectors: Lebesgue pairings as weighted inner products -/

theorem integral_wMeasure (M : ℝ) (g : ℂ → ℂ) :
    ∫ y, g y ∂wMeasure M = ∫ y, density M y • g y :=
  integral_withDensity_eq_integral_smul (measurable_density M) g

theorem integrable_wMeasure_iff (M : ℝ) {g : ℂ → ℂ} :
    Integrable g (wMeasure M) ↔ Integrable (fun y => density M y • g y) volume :=
  integrable_withDensity_iff_integrable_smul (measurable_density M)

/-- The weighted representative `conj ψ / ⟨y⟩^{2M}` of the Lebesgue pairing with `ψ`. -/
def dualFun (M : ℝ) (ψ : ℂ → ℂ) (y : ℂ) : ℂ :=
  star (ψ y) * (((density M y : ℝ)⁻¹ : ℝ) : ℂ)

/-- The element of `L²(⟨y⟩^{2M}dy)` representing `F ↦ ∫ F ψ dy`, when it is square integrable. -/
def dualVec (M : ℝ) (ψ : ℂ → ℂ) (h : MemLp (dualFun M ψ) 2 (wMeasure M)) : L2w M :=
  h.toLp _

theorem density_smul_dualFun (M : ℝ) (ψ : ℂ → ℂ) (z : ℂ) (y : ℂ) :
    density M y • (star (dualFun M ψ y) * z) = z * ψ y := by
  have hρ : ((density M y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (density_pos M y).ne'
  rw [NNReal.smul_def, Complex.real_smul, dualFun]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  push_cast
  field_simp

/-- The Lebesgue pairing `∫ F ψ dy` is the weighted inner product with `dualVec`. -/
theorem inner_dualVec (M : ℝ) {ψ : ℂ → ℂ} (h : MemLp (dualFun M ψ) 2 (wMeasure M))
    (F : L2w M) : inner ℂ (dualVec M ψ h) F = ∫ y, F y * ψ y := by
  rw [L2.inner_def]
  have h1 : (fun y => inner ℂ ((dualVec M ψ h : ℂ → ℂ) y) (F y)) =ᵐ[wMeasure M]
      fun y => star (dualFun M ψ y) * F y := by
    filter_upwards [MemLp.coeFn_toLp h] with y hy
    rw [dualVec, hy, RCLike.inner_apply']
    rfl
  rw [integral_congr_ae h1, integral_wMeasure]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => density_smul_dualFun M ψ (F y) y)

/-- The Lebesgue pairing is absolutely convergent. -/
theorem integrable_mul_of_dualFun (M : ℝ) {ψ : ℂ → ℂ} (h : MemLp (dualFun M ψ) 2 (wMeasure M))
    (F : L2w M) : Integrable (fun y => F y * ψ y) volume := by
  have h0 := L2.integrable_inner (𝕜 := ℂ) (dualVec M ψ h) F
  have h1 : (fun y => inner ℂ ((dualVec M ψ h : ℂ → ℂ) y) (F y)) =ᵐ[wMeasure M]
      fun y => star (dualFun M ψ y) * F y := by
    filter_upwards [MemLp.coeFn_toLp h] with y hy
    rw [dualVec, hy, RCLike.inner_apply']
    rfl
  have h2 := h0.congr h1
  rw [integrable_wMeasure_iff] at h2
  exact h2.congr (Filter.Eventually.of_forall fun y => density_smul_dualFun M ψ (F y) y)

/-- Test functions give square-integrable dual vectors for every weight exponent. -/
theorem memLp_dualFun_testFn (M : ℝ) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    MemLp (dualFun M φ) 2 (wMeasure M) := by
  have hc : Continuous (dualFun M φ) := by
    unfold dualFun
    exact (hφ.continuous.star).mul (Complex.continuous_ofReal.comp
      ((continuous_coe_density M).inv₀ fun y => (density_pos M y).ne'))
  refine hc.memLp_of_hasCompactSupport ?_
  have hs : HasCompactSupport fun y => star (φ y) := hφ.compact.comp_left (by simp)
  exact hs.mul_right

/-! ### The weighted Sobolev space `H^j_M` -/

/-- The multi-indices `α = (α₁, α₂)` with `|α| ≤ j` (same index set as
`NonUniqueEuler/Defs/Infra/SobolevSpace.lean`, `SobIdx`). -/
abbrev Idx (j : ℕ) : Type := ↥(multiIdx j)

/-- The multi-index `0`. -/
def idx0 (j : ℕ) : Idx j := ⟨(0, 0), zero_mem_multiIdx j⟩

/-- Tuples `(F_α)_{|α| ≤ j}` in `L²(⟨y⟩^{2M} dy)` with the square-sum norm. -/
abbrev Tuple (j : ℕ) (M : ℝ) : Type := PiLp 2 (fun _ : Idx j => L2w M)

/-- Complex test functions on the plane. -/
abbrev TestFn : Type := {φ : ℂ → ℂ // IsTestFn univ φ}

/-- The weighted vector representing `F ↦ ∫ F φ dy` for a test function `φ`. -/
def testVec (M : ℝ) (φ : TestFn) : L2w M :=
  dualVec M φ.1 (memLp_dualFun_testFn M φ.2)

theorem inner_testVec (M : ℝ) (φ : TestFn) (F : L2w M) :
    inner ℂ (testVec M φ) F = ∫ y, F y * φ.1 y :=
  inner_dualVec M _ F

/-- The derivative `∂^α φ` of a test function, as a test function. -/
def TestFn.partial (α : ℕ × ℕ) (φ : TestFn) : TestFn := ⟨partialD α φ.1, φ.2.partialD α⟩

/-- The continuous functional
`F ↦ ∫ F_0 ∂^α φ dy - (-1)^{|α|} ∫ F_α φ dy`; it vanishes for all `φ` iff `F_α = ∂^α F_0`
weakly (kernel-intersection design adapted from
`NonUniqueEuler/Defs/Infra/SobolevSpace.lean`, `weakFunctional`). -/
def weakFunctional (j : ℕ) (M : ℝ) (α : Idx j) (φ : TestFn) : Tuple j M →L[ℂ] ℂ :=
  (innerSL ℂ (testVec M (φ.partial α.1))).comp (PiLp.proj 2 (fun _ : Idx j => L2w M) (idx0 j)) -
    ((-1 : ℂ) ^ (pdList α.1).length) •
      (innerSL ℂ (testVec M φ)).comp (PiLp.proj 2 (fun _ : Idx j => L2w M) α)

theorem weakFunctional_apply (j : ℕ) (M : ℝ) (α : Idx j) (φ : TestFn) (F : Tuple j M) :
    weakFunctional j M α φ F =
      (∫ y, (F.ofLp (idx0 j) : ℂ → ℂ) y * partialD α.1 φ.1 y) -
        (-1 : ℂ) ^ (pdList α.1).length * ∫ y, (F.ofLp α : ℂ → ℂ) y * φ.1 y := by
  simp only [weakFunctional, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply, smul_eq_mul]
  rw [inner_testVec, inner_testVec]
  rfl

/-- `H^j_M` as a submodule of the tuple space: tuples with `F_α = ∂^α F_0` weakly. -/
def HSub (j : ℕ) (M : ℝ) : Submodule ℂ (Tuple j M) :=
  ⨅ (α : Idx j) (φ : TestFn), LinearMap.ker (weakFunctional j M α φ : Tuple j M →ₗ[ℂ] ℂ)

/-- Membership in `HSub j M` is exactly: each `F_α` is the distributional derivative
`∂^α F_0` (`HasWeakDerivOn` of `NonUniqueEuler.Defs.Infra.Sobolev`). -/
theorem mem_HSub_iff {j : ℕ} {M : ℝ} (F : Tuple j M) :
    F ∈ HSub j M ↔ ∀ α : Idx j,
      HasWeakDerivOn univ (pdList α.1) (F.ofLp (idx0 j) : ℂ → ℂ) (F.ofLp α : ℂ → ℂ) := by
  simp only [HSub, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    weakFunctional_apply, sub_eq_zero, HasWeakDerivOn, partialD]
  constructor
  · intro h α φ hφ
    exact h α ⟨φ, hφ⟩
  · intro h α φ
    exact h α φ.1 φ.2

theorem isClosed_HSub (j : ℕ) (M : ℝ) : IsClosed (HSub j M : Set (Tuple j M)) := by
  rw [HSub, Submodule.coe_iInf]
  refine isClosed_iInter fun α => ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (weakFunctional j M α φ).isClosed_ker

/-- **The weighted Sobolev space `H^j_M`** (`paper/main.tex:655`): the complex Hilbert space of
`f` with `⟨y⟩^M ∂^α f ∈ L²(ℝ²)` for all `|α| ≤ j`, derivatives distributional, stored with all
its derivatives `(∂^α f)_{|α| ≤ j}`; the norm is `(∑_{|α| ≤ j} ‖⟨y⟩^M ∂^α f‖²_{L²})^{1/2}`
(`HjM.norm_sq`). -/
abbrev HjM (j : ℕ) (M : ℝ) : Type := ↥(HSub j M)

/-- `H^j_M` is complete (`paper/main.tex:660`, "complex Hilbert spaces"). -/
instance HjM.completeSpace (j : ℕ) (M : ℝ) : CompleteSpace (HjM j M) :=
  (isClosed_HSub j M).completeSpace_coe

example (j : ℕ) (M : ℝ) : InnerProductSpace ℂ (HjM j M) := inferInstance

namespace HjM

variable {j : ℕ} {M : ℝ}

/-- The function `f = F_0` of an element of `H^j_M`, as an element of `L²(⟨y⟩^{2M}dy)`. -/
def value (F : HjM j M) : L2w M := (F : Tuple j M).ofLp (idx0 j)

/-- The distributional derivative `∂^α f = F_α`. -/
def der (F : HjM j M) (α : Idx j) : L2w M := (F : Tuple j M).ofLp α

variable (j M) in
/-- The value map `H^j_M → L²(⟨y⟩^{2M}dy)` is continuous and linear. -/
def valueCLM : HjM j M →L[ℂ] L2w M :=
  (PiLp.proj 2 (fun _ : Idx j => L2w M) (idx0 j)).comp (HSub j M).subtypeL

variable (j M) in
/-- The derivative maps `H^j_M → L²(⟨y⟩^{2M}dy)` are continuous and linear. -/
def derCLM (α : Idx j) : HjM j M →L[ℂ] L2w M :=
  (PiLp.proj 2 (fun _ : Idx j => L2w M) α).comp (HSub j M).subtypeL

@[simp] theorem valueCLM_apply (F : HjM j M) : valueCLM j M F = F.value := rfl

@[simp] theorem derCLM_apply (α : Idx j) (F : HjM j M) : derCLM j M α F = F.der α := rfl

@[simp] theorem der_idx0 (F : HjM j M) : F.der (idx0 j) = F.value := rfl

theorem value_add (F G : HjM j M) : (F + G).value = F.value + G.value := rfl

theorem value_smul (c : ℂ) (F : HjM j M) : (c • F).value = c • F.value := rfl

theorem value_zero : (0 : HjM j M).value = 0 := rfl

/-- The stored components are the distributional derivatives of the value. -/
theorem hasWeakDeriv (F : HjM j M) (α : Idx j) :
    HasWeakDerivOn univ (pdList α.1) (F.value : ℂ → ℂ) (F.der α : ℂ → ℂ) :=
  (mem_HSub_iff (F : Tuple j M)).1 F.2 α

/-- Each `∂^α f`, `|α| ≤ j`, satisfies `⟨y⟩^M ∂^α f ∈ L²(ℝ²)` (`paper/main.tex:655`). -/
theorem memLp_der (F : HjM j M) (α : Idx j) :
    MemLp (fun y => bracket y ^ M • (F.der α : ℂ → ℂ) y) 2 volume :=
  (memLp_wMeasure_iff M).1 (Lp.memLp _)

/-- The function itself satisfies `⟨y⟩^M f ∈ L²(ℝ²)`. -/
theorem memLp_value (F : HjM j M) :
    MemLp (fun y => bracket y ^ M • (F.value : ℂ → ℂ) y) 2 volume :=
  F.memLp_der (idx0 j)

/-- The sum-of-squares norm (`paper/main.tex:660`): `‖F‖² = ∑_{|α| ≤ j} ‖∂^α f‖²`. -/
theorem norm_sq (F : HjM j M) : ‖F‖ ^ 2 = ∑ α : Idx j, ‖F.der α‖ ^ 2 := by
  rw [Submodule.coe_norm, PiLp.norm_sq_eq_of_L2]
  rfl

/-- The sum-of-squares norm written with the weight:
`‖F‖² = ∑_{|α| ≤ j} ‖⟨y⟩^M ∂^α f‖²_{L²(ℝ²)}` (`paper/main.tex:655`, `660`). -/
theorem norm_sq_eq_weighted (F : HjM j M) :
    ‖F‖ ^ 2 = ∑ α : Idx j,
      ((eLpNorm (fun y => bracket y ^ M • (F.der α : ℂ → ℂ) y) 2 volume).toReal) ^ 2 := by
  rw [norm_sq]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [norm_L2w]

/-- The Hilbert inner product sums the weighted `L²` products of all derivatives. -/
theorem inner_eq (F G : HjM j M) :
    inner ℂ F G = ∑ α : Idx j, inner ℂ (F.der α) (G.der α) := by
  rw [Submodule.coe_inner, PiLp.inner_apply]
  rfl

end HjM

/-! ### `M > 1`: the integral is a bounded functional -/

/-- The reciprocal weight `⟨y⟩^{-2M}` as a complex function. -/
def invWeight (M : ℝ) (y : ℂ) : ℂ := (((density M y : ℝ)⁻¹ : ℝ) : ℂ)

theorem dualFun_one (M : ℝ) : dualFun M (fun _ => (1 : ℂ)) = invWeight M := by
  funext y
  simp [dualFun, invWeight]

theorem inv_density_eq (M : ℝ) (y : ℂ) : (density M y : ℝ)⁻¹ = (1 + ‖y‖ ^ 2) ^ (-M) := by
  rw [coe_density, Real.rpow_neg (one_add_norm_sq_pos y).le]

theorem norm_sq_bracket_smul_invWeight (M : ℝ) (y : ℂ) :
    ‖bracket y ^ M • invWeight M y‖ ^ 2 = (1 + ‖y‖ ^ 2) ^ (-M) := by
  have hb : 0 < bracket y ^ M := Real.rpow_pos_of_pos (bracket_pos y) M
  have hρ : 0 < (density M y : ℝ) := density_pos M y
  rw [norm_smul, invWeight, Complex.norm_real, Real.norm_of_nonneg hb.le,
    Real.norm_of_nonneg (inv_nonneg.2 hρ.le), mul_pow, bracket_rpow_sq, ← coe_density,
    ← inv_density_eq]
  field_simp

/-- `∫_{ℝ²} ⟨y⟩^{-2M} dy < ∞` for `M > 1` (`paper/main.tex:660`, "`M > 1` makes the integral
bounded"); Mathlib's `integrable_rpow_neg_one_add_norm_sq` in dimension two. -/
theorem integrable_inv_weight {M : ℝ} (hM : 1 < M) :
    Integrable (fun y : ℂ => (1 + ‖y‖ ^ 2) ^ (-M)) volume := by
  have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℂ)) (r := 2 * M)
    (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  congr 1
  ring

theorem memLp_invWeight {M : ℝ} (hM : 1 < M) : MemLp (invWeight M) 2 (wMeasure M) := by
  rw [memLp_wMeasure_iff]
  have hc : Continuous fun y => bracket y ^ M • invWeight M y := by
    unfold invWeight
    exact (continuous_bracket_rpow M).smul (Complex.continuous_ofReal.comp
      ((continuous_coe_density M).inv₀ fun y => (density_pos M y).ne'))
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  exact (integrable_inv_weight hM).congr
    (Filter.Eventually.of_forall fun y => (norm_sq_bracket_smul_invWeight M y).symm)

theorem memLp_dualFun_one {M : ℝ} (hM : 1 < M) :
    MemLp (dualFun M (fun _ => (1 : ℂ))) 2 (wMeasure M) := by
  rw [dualFun_one]
  exact memLp_invWeight hM

/-- The representative of `f ↦ ∫ f` in `L²(⟨y⟩^{2M}dy)`. -/
def decayVec (M : ℝ) (hM : 1 < M) : L2w M := dualVec M (fun _ => 1) (memLp_dualFun_one hM)

/-- The integral `f ↦ ∫_{ℝ²} f dy` as a bounded linear functional on
`H^0_M = L²(⟨y⟩^{2M}dy)`, for `M > 1` (`paper/main.tex:660`). -/
def integralCLM (M : ℝ) (hM : 1 < M) : L2w M →L[ℂ] ℂ := innerSL ℂ (decayVec M hM)

/-- For `M > 1` every `f` with `⟨y⟩^M f ∈ L²` is Lebesgue integrable on `ℝ²`. -/
theorem integrable_L2w {M : ℝ} (hM : 1 < M) (F : L2w M) : Integrable (F : ℂ → ℂ) volume := by
  simpa using integrable_mul_of_dualFun M (memLp_dualFun_one hM) F

theorem integralCLM_apply {M : ℝ} (hM : 1 < M) (F : L2w M) :
    integralCLM M hM F = ∫ y, F y := by
  rw [integralCLM, innerSL_apply_apply, decayVec, inner_dualVec]
  simp

/-- The constant `C_M = (∫_{ℝ²} ⟨y⟩^{-2M} dy)^{1/2}`. -/
def CM (M : ℝ) : ℝ := Real.sqrt (∫ y : ℂ, (1 + ‖y‖ ^ 2) ^ (-M))

theorem coeFn_decayVec_ae {M : ℝ} (hM : 1 < M) :
    (decayVec M hM : ℂ → ℂ) =ᵐ[wMeasure M] invWeight M := by
  exact (MemLp.coeFn_toLp (memLp_dualFun_one hM)).trans
    (Filter.Eventually.of_forall fun y => congrFun (dualFun_one M) y)

theorem norm_decayVec {M : ℝ} (hM : 1 < M) : ‖decayVec M hM‖ = CM M := by
  have hsq : ‖decayVec M hM‖ ^ 2 = ∫ y : ℂ, (1 + ‖y‖ ^ 2) ^ (-M) := by
    rw [@norm_sq_eq_re_inner ℂ, decayVec, inner_dualVec]
    have hae : (fun y => (dualVec M (fun _ => (1 : ℂ)) (memLp_dualFun_one hM) : ℂ → ℂ) y * 1)
        =ᵐ[volume] fun y => (((1 + ‖y‖ ^ 2) ^ (-M) : ℝ) : ℂ) := by
      filter_upwards [(volume_ac M).ae_le (coeFn_decayVec_ae hM)] with y hy
      rw [mul_one]
      change (decayVec M hM : ℂ → ℂ) y = _
      rw [hy, invWeight, inv_density_eq]
    rw [integral_congr_ae hae, integral_complex_ofReal]
    simp
  rw [CM, ← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Boundedness of the integral (`paper/main.tex:660`): `|∫ f| ≤ C_M ‖⟨y⟩^M f‖_{L²}`. -/
theorem norm_integral_le {M : ℝ} (hM : 1 < M) (F : L2w M) :
    ‖∫ y, F y‖ ≤ CM M * ‖F‖ := by
  rw [← integralCLM_apply hM, integralCLM, innerSL_apply_apply, ← norm_decayVec hM]
  exact norm_inner_le_norm _ _

theorem lintegral_wMeasure (M : ℝ) (g : ℂ → ℝ≥0∞) :
    ∫⁻ y, g y ∂wMeasure M = ∫⁻ y, (density M y : ℝ≥0∞) * g y :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_density M).coe_nnreal_ennreal
    (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top) g

/-- The `L¹` bound behind `paper/main.tex:660`: `‖f‖_{L¹} ≤ C_M ‖⟨y⟩^M f‖_{L²}` for `M > 1`
(Cauchy–Schwarz against `⟨y⟩^{-M}`). -/
theorem integral_norm_le {M : ℝ} (hM : 1 < M) (F : L2w M) :
    ∫ y, ‖F y‖ ≤ CM M * ‖F‖ := by
  have hw := memLp_invWeight hM
  have hF : AEStronglyMeasurable (F : ℂ → ℂ) (wMeasure M) := Lp.aestronglyMeasurable F
  have key : ∫⁻ y, ‖F y‖ₑ = eLpNorm (invWeight M • (F : ℂ → ℂ)) 1 (wMeasure M) := by
    rw [eLpNorm_one_eq_lintegral_enorm, lintegral_wMeasure]
    refine lintegral_congr fun y => ?_
    have hρ : 0 < (density M y : ℝ) := density_pos M y
    simp only [smul_eq_mul, Pi.mul_apply, invWeight]
    rw [enorm_mul, ← ofReal_norm (((density M y : ℝ)⁻¹ : ℝ) : ℂ), Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 hρ.le), ← mul_assoc, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), mul_inv_cancel₀ hρ.ne', ENNReal.ofReal_one,
      one_mul]
  have hH : eLpNorm (invWeight M • (F : ℂ → ℂ)) 1 (wMeasure M) ≤
      eLpNorm (invWeight M) 2 (wMeasure M) * eLpNorm F 2 (wMeasure M) :=
    eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hF hw.1
  have hfin : eLpNorm (invWeight M) 2 (wMeasure M) * eLpNorm F 2 (wMeasure M) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top hw.eLpNorm_ne_top (Lp.eLpNorm_ne_top F)
  rw [integral_norm_eq_lintegral_enorm (hF.mono_ac (volume_ac M)), key]
  calc _ ≤ (eLpNorm (invWeight M) 2 (wMeasure M) * eLpNorm F 2 (wMeasure M)).toReal :=
        ENNReal.toReal_mono hfin hH
    _ = CM M * ‖F‖ := by
      rw [ENNReal.toReal_mul, Lp.norm_def, ← norm_decayVec hM, Lp.norm_def,
        eLpNorm_congr_ae (coeFn_decayVec_ae hM)]

/-! ### Local integrability and uniqueness of the stored derivatives -/

/-- Every element of `L²(⟨y⟩^{2M}dy)` is locally Lebesgue integrable (any real `M`). -/
theorem locallyIntegrable_L2w (M : ℝ) (F : L2w M) : LocallyIntegrable (F : ℂ → ℂ) volume := by
  intro x
  let b : ContDiffBump x := ⟨1, 2, one_pos, one_lt_two⟩
  have hφ : IsTestFn univ (fun y => ((b y : ℝ) : ℂ)) :=
    WeakDerivAux.isTestFn_ofReal b.contDiff b.hasCompactSupport (subset_univ _)
  have hint := integrable_mul_of_dualFun M (memLp_dualFun_testFn M hφ) F
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  refine hint.integrableOn.congr_fun (fun y hy => ?_) Metric.isOpen_ball.measurableSet
  have h1 : b y = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  simp only [h1, Complex.ofReal_one, mul_one]

theorem coeFn_toLp_volume {M : ℝ} {f : ℂ → ℂ} (h : MemLp f 2 (wMeasure M)) :
    (h.toLp f : ℂ → ℂ) =ᵐ[volume] f :=
  (volume_ac M).ae_le h.coeFn_toLp

namespace HjM

variable {j : ℕ} {M : ℝ}

/-- An element of `H^j_M` is determined by its function: weak derivatives are unique. -/
theorem value_injective : Function.Injective (value : HjM j M → L2w M) := by
  intro F G h
  have hd (α : Idx j) : F.der α = G.der α := by
    have hG := G.hasWeakDeriv α
    rw [← h] at hG
    have hae := HasWeakDerivOn.ae_eq isOpen_univ
      ((locallyIntegrable_L2w M (F.der α)).locallyIntegrableOn _)
      ((locallyIntegrable_L2w M (G.der α)).locallyIntegrableOn _) (F.hasWeakDeriv α) hG
    apply Lp.ext
    exact (wMeasure_ac M).ae_le (hae.mono fun x hx => hx (mem_univ x))
  apply Subtype.ext
  apply (WithLp.ext_iff (p := 2)).mpr
  funext α
  exact hd α

@[ext] theorem ext {F G : HjM j M} (h : F.value = G.value) : F = G :=
  value_injective h

/-- `‖f‖_{L²(⟨y⟩^{2M})} ≤ ‖f‖_{H^j_M}`. -/
theorem norm_value_le (F : HjM j M) : ‖F.value‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : Tuple j M) (idx0 j)

variable (j M) in
/-- The integral `f ↦ ∫_{ℝ²} f` as a bounded functional on `H^j_M`, `M > 1`. -/
def integralFunctional (hM : 1 < M) : HjM j M →L[ℂ] ℂ :=
  (integralCLM M hM).comp (valueCLM j M)

theorem integralFunctional_apply (hM : 1 < M) (F : HjM j M) :
    integralFunctional j M hM F = ∫ y, F.value y := by
  simp [integralFunctional, integralCLM_apply]

theorem integrable_value (hM : 1 < M) (F : HjM j M) : Integrable (F.value : ℂ → ℂ) volume :=
  integrable_L2w hM F.value

theorem norm_integral_le (hM : 1 < M) (F : HjM j M) : ‖∫ y, F.value y‖ ≤ CM M * ‖F‖ :=
  (B0008.norm_integral_le hM F.value).trans
    (mul_le_mul_of_nonneg_left (norm_value_le F) (Real.sqrt_nonneg _))

end HjM

/-! ### Function-level membership -/

/-- The manuscript's membership `f ∈ H^j_M` (`paper/main.tex:655`), stated for a function:
`⟨y⟩^M f ∈ L²(ℝ²)`, and for every `|α| ≤ j` a distributional derivative `∂^α f = g` with
`⟨y⟩^M g ∈ L²(ℝ²)`. -/
structure MemHjM (j : ℕ) (M : ℝ) (f : ℂ → ℂ) : Prop where
  memLp : MemLp (fun y => bracket y ^ M • f y) 2 volume
  deriv : ∀ α ∈ multiIdx j, ∃ g : ℂ → ℂ,
    MemLp (fun y => bracket y ^ M • g y) 2 volume ∧ HasWeakDerivOn univ (pdList α) f g

theorem MemHjM.congr_ae {j : ℕ} {M : ℝ} {f f' : ℂ → ℂ} (h : MemHjM j M f)
    (hff : f =ᵐ[volume] f') : MemHjM j M f' := by
  refine ⟨h.memLp.ae_eq ?_, fun α hα => ?_⟩
  · filter_upwards [hff] with y hy
    rw [hy]
  · obtain ⟨g, hg, hfg⟩ := h.deriv α hα
    refine ⟨g, hg, hfg.congr_ae ?_ (Filter.Eventually.of_forall fun _ _ => rfl)⟩
    filter_upwards [hff] with y hy _
    exact hy

namespace HjM

variable {j : ℕ} {M : ℝ}

/-- The function of an element of `H^j_M` satisfies the manuscript's membership. -/
theorem memHjM (F : HjM j M) : MemHjM j M (F.value : ℂ → ℂ) :=
  ⟨F.memLp_value, fun α hα => ⟨F.der ⟨α, hα⟩, F.memLp_der _, F.hasWeakDeriv ⟨α, hα⟩⟩⟩

open Classical in
/-- The tuple `(∂^α f)_{|α| ≤ j}` of a function satisfying `MemHjM`. -/
def tupleOf {f : ℂ → ℂ} (h : MemHjM j M f) : Tuple j M :=
  WithLp.toLp 2 fun α : Idx j =>
    if α = idx0 j then ((memLp_wMeasure_iff M).2 h.memLp).toLp f
    else ((memLp_wMeasure_iff M).2 (h.deriv α.1 α.2).choose_spec.1).toLp _

theorem tupleOf_idx0 {f : ℂ → ℂ} (h : MemHjM j M f) :
    (tupleOf h).ofLp (idx0 j) = ((memLp_wMeasure_iff M).2 h.memLp).toLp f := by
  simp [tupleOf]

theorem tupleOf_mem {f : ℂ → ℂ} (h : MemHjM j M f) : tupleOf h ∈ HSub j M := by
  rw [mem_HSub_iff]
  intro α
  have h0 : ((tupleOf h).ofLp (idx0 j) : ℂ → ℂ) =ᵐ[volume] f := by
    rw [tupleOf_idx0]
    exact coeFn_toLp_volume _
  by_cases hα : α = idx0 j
  · subst hα
    intro φ _
    simp [idx0, pdList]
  · have hT : (tupleOf h).ofLp α =
        ((memLp_wMeasure_iff M).2 (h.deriv α.1 α.2).choose_spec.1).toLp _ := by
      simp [tupleOf, hα]
    rw [hT]
    refine (h.deriv α.1 α.2).choose_spec.2.congr_ae ?_ ?_
    · filter_upwards [h0] with y hy _
      exact hy.symm
    · filter_upwards [coeFn_toLp_volume ((memLp_wMeasure_iff M).2
        (h.deriv α.1 α.2).choose_spec.1)] with y hy _
      exact hy.symm

/-- The pairings in the weak-derivative identities are absolutely convergent. -/
theorem integrable_pairing (F : HjM j M) (α : Idx j) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    Integrable (fun y => (F.der α : ℂ → ℂ) y * φ y) volume :=
  integrable_mul_of_dualFun M (memLp_dualFun_testFn M hφ) _

/-- The element of `H^j_M` defined by a function satisfying the manuscript's membership. -/
def ofMemHjM {f : ℂ → ℂ} (h : MemHjM j M f) : HjM j M := ⟨tupleOf h, tupleOf_mem h⟩

theorem value_ofMemHjM {f : ℂ → ℂ} (h : MemHjM j M f) :
    ((ofMemHjM h).value : ℂ → ℂ) =ᵐ[volume] f := by
  change ((tupleOf h).ofLp (idx0 j) : ℂ → ℂ) =ᵐ[volume] f
  rw [tupleOf_idx0]
  exact coeFn_toLp_volume _

end HjM

/-- **Membership lemma for `H^j_M`**: a function `f` has `⟨y⟩^M ∂^α f ∈ L²` for all
`|α| ≤ j` (distributional derivatives) iff it is (a.e.) the function of an element of the
Hilbert space `HjM j M` (`paper/main.tex:655`). -/
theorem memHjM_iff {j : ℕ} {M : ℝ} (f : ℂ → ℂ) :
    MemHjM j M f ↔ ∃ F : HjM j M, (F.value : ℂ → ℂ) =ᵐ[volume] f :=
  ⟨fun h => ⟨HjM.ofMemHjM h, HjM.value_ofMemHjM h⟩,
    fun ⟨F, hF⟩ => F.memHjM.congr_ae hF⟩

/-- Non-vacuity: every test function lies in `H^j_M`, with its classical derivatives. -/
theorem memHjM_of_testFn (j : ℕ) (M : ℝ) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    MemHjM j M φ := by
  have hL (g : ℂ → ℂ) (hg : IsTestFn univ g) :
      MemLp (fun y => bracket y ^ M • g y) 2 volume := by
    have hc : Continuous fun y => bracket y ^ M • g y :=
      (continuous_bracket_rpow M).smul hg.continuous
    exact hc.memLp_of_hasCompactSupport (hg.compact.smul_left (f := fun y => bracket y ^ M))
  refine ⟨hL φ hφ, fun α _ => ⟨partialD α φ, hL _ (hφ.partialD α), ?_⟩⟩
  exact hasWeakDerivOn_of_contDiffOn isOpen_univ (n := (pdList α).length) le_rfl
    (contDiff_infty.1 hφ.smooth _).contDiffOn

/-! ### The zero-mean subspace `X_{j,M}` -/

/-- **The zero-mean space `X_{j,M} = {f ∈ H^j_M : ∫_{ℝ²} f = 0}`** (`paper/main.tex:657`). The
integrability of `f` is part of the condition; for `M > 1` it is automatic
(`HjM.integrable_value`), and `X_{j,M}` is the kernel of a bounded functional (`XjM_eq_ker`). -/
def XjM (j : ℕ) (M : ℝ) : Submodule ℂ (HjM j M) where
  carrier := {F | Integrable (F.value : ℂ → ℂ) volume ∧ ∫ y, F.value y = 0}
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    have hae : ((F + G).value : ℂ → ℂ) =ᵐ[volume] fun y => F.value y + G.value y :=
      (volume_ac M).ae_le (Lp.coeFn_add F.value G.value)
    refine ⟨(hF.add hG).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_add hF hG, hF0, hG0, add_zero]
  zero_mem' := by
    have hae : ((0 : HjM j M).value : ℂ → ℂ) =ᵐ[volume] fun _ => (0 : ℂ) :=
      (volume_ac M).ae_le (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := wMeasure M))
    refine ⟨(integrable_zero ℂ ℂ volume).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_zero]
  smul_mem' := by
    rintro c F ⟨hF, hF0⟩
    have hae : ((c • F).value : ℂ → ℂ) =ᵐ[volume] fun y => c • F.value y :=
      (volume_ac M).ae_le (Lp.coeFn_smul c F.value)
    refine ⟨(hF.smul c).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_smul, hF0, smul_zero]

theorem mem_XjM_iff {j : ℕ} {M : ℝ} (hM : 1 < M) (F : HjM j M) :
    F ∈ XjM j M ↔ ∫ y, F.value y = 0 :=
  ⟨fun h => h.2, fun h => ⟨HjM.integrable_value hM F, h⟩⟩

/-- For `M > 1`, `X_{j,M}` is the kernel of the bounded functional `f ↦ ∫ f`. -/
theorem XjM_eq_ker {j : ℕ} {M : ℝ} (hM : 1 < M) :
    XjM j M = LinearMap.ker (HjM.integralFunctional j M hM : HjM j M →ₗ[ℂ] ℂ) := by
  ext F
  rw [mem_XjM_iff hM, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    HjM.integralFunctional_apply]

/-- **`X_{j,M}` is a closed subspace of `H^j_M`** for `M > 1` (`paper/main.tex:657`, `660`). -/
theorem isClosed_XjM {j : ℕ} {M : ℝ} (hM : 1 < M) : IsClosed (XjM j M : Set (HjM j M)) := by
  rw [XjM_eq_ker hM]
  exact (HjM.integralFunctional j M hM).isClosed_ker

/-- `X_{j,M}` is a complex Hilbert space for `M > 1`. -/
theorem completeSpace_XjM {j : ℕ} {M : ℝ} (hM : 1 < M) : CompleteSpace (XjM j M) :=
  (isClosed_XjM hM).completeSpace_coe

instance {j : ℕ} {M : ℝ} [Fact (1 < M)] : CompleteSpace (XjM j M) :=
  completeSpace_XjM Fact.out

example {j : ℕ} {M : ℝ} : InnerProductSpace ℂ (XjM j M) := inferInstance

end UnforcedLeray.B0008
