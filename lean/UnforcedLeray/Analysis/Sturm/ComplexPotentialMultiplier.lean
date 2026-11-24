import UnforcedLeray.Analysis.Sturm.PotentialMultiplier

/-!
# Actual Gaussian potential multiplication on complex L²(ℝ)

This is the complex L² counterpart of `PotentialMultiplier`, compatible with
the complex-valued Yukawa kernel construction. The coefficient remains the
actual real Gaussian potential. Its explicit square-root multiplier squares
to the potential operator; no abstract substitute potential is introduced.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace UnforcedLeray.Sturm
open GaussianPotential

abbrev ComplexSturmL2 := Lp ℂ 2 (volume : Measure ℝ)

namespace ComplexBoundedMultiplier

variable (w : ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hbound : ∀ x, ‖w x‖ ≤ C)
include hw C hbound

theorem memLp_mul (f : ComplexSturmL2) : MemLp (fun x => (w x : ℂ) * f x) 2 volume := by
  refine (Lp.memLp f).of_le_mul (c := C)
    ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

def apply (f : ComplexSturmL2) : ComplexSturmL2 :=
  (memLp_mul w hw C hbound f).toLp (fun x => (w x : ℂ) * f x)

theorem coeFn_apply (f : ComplexSturmL2) :
    apply w hw C hbound f =ᵐ[volume] (fun x => (w x : ℂ) * f x) :=
  (memLp_mul w hw C hbound f).coeFn_toLp

def linearMap : ComplexSturmL2 →ₗ[ℂ] ComplexSturmL2 where
  toFun := apply w hw C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_apply w hw C hbound (f + g), Lp.coeFn_add f g,
      Lp.coeFn_add (apply w hw C hbound f) (apply w hw C hbound g),
      coeFn_apply w hw C hbound f, coeFn_apply w hw C hbound g] with x hfg ha hb hf hg
    simp only [Pi.add_apply] at ha hb
    rw [hfg, ha, hb, hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_apply w hw C hbound (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul c (apply w hw C hbound f), coeFn_apply w hw C hbound f] with x hcf ha hb hf
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply, smul_eq_mul] at ha hb
    rw [hcf, ha, hb, hf]
    ring

theorem norm_apply_le (f : ComplexSturmL2) : ‖apply w hw C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_apply w hw C hbound f] with x hx
  rw [hx, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

def operator : ComplexSturmL2 →L[ℂ] ComplexSturmL2 :=
  (linearMap w hw C hbound).mkContinuous C (norm_apply_le w hw C hbound)

theorem coeFn_operator (f : ComplexSturmL2) :
    operator w hw C hbound f =ᵐ[volume] (fun x => (w x : ℂ) * f x) :=
  coeFn_apply w hw C hbound f

theorem norm_operator_le (hC : 0 ≤ C) : ‖operator w hw C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem operator_isSelfAdjoint : IsSelfAdjoint (operator w hw C hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪operator w hw C hbound f, g⟫_ℂ = ⟪f, operator w hw C hbound g⟫_ℂ
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_operator w hw C hbound f, coeFn_operator w hw C hbound g] with x hf hg
  simp only [RCLike.inner_apply, hf, hg, map_mul, Complex.conj_ofReal]
  ring

end ComplexBoundedMultiplier

/-- Actual real Gaussian potential acting on complex L². -/
def complexPotentialOperator : ComplexSturmL2 →L[ℂ] ComplexSturmL2 :=
  ComplexBoundedMultiplier.operator Wlog measurable_Wlog 8 norm_Wlog_le_eight

theorem coeFn_complexPotentialOperator (f : ComplexSturmL2) :
    complexPotentialOperator f =ᵐ[volume] (fun x => (Wlog x : ℂ) * f x) :=
  ComplexBoundedMultiplier.coeFn_operator Wlog measurable_Wlog 8 norm_Wlog_le_eight f

theorem norm_complexPotentialOperator_le : ‖complexPotentialOperator‖ ≤ 8 :=
  ComplexBoundedMultiplier.norm_operator_le Wlog measurable_Wlog 8 norm_Wlog_le_eight (by norm_num)

theorem complexPotentialOperator_isSelfAdjoint : IsSelfAdjoint complexPotentialOperator :=
  ComplexBoundedMultiplier.operator_isSelfAdjoint Wlog measurable_Wlog 8 norm_Wlog_le_eight

/-- Actual pointwise square root of the Gaussian potential acting on complex L². -/
def complexPotentialSqrtOperator : ComplexSturmL2 →L[ℂ] ComplexSturmL2 :=
  ComplexBoundedMultiplier.operator sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le

theorem coeFn_complexPotentialSqrtOperator (f : ComplexSturmL2) :
    complexPotentialSqrtOperator f =ᵐ[volume] (fun x => (sqrtPotential x : ℂ) * f x) :=
  ComplexBoundedMultiplier.coeFn_operator sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le f

theorem norm_complexPotentialSqrtOperator_le : ‖complexPotentialSqrtOperator‖ ≤ Real.sqrt 8 :=
  ComplexBoundedMultiplier.norm_operator_le sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le (Real.sqrt_nonneg _)

theorem complexPotentialSqrtOperator_isSelfAdjoint : IsSelfAdjoint complexPotentialSqrtOperator :=
  ComplexBoundedMultiplier.operator_isSelfAdjoint sqrtPotential measurable_sqrtPotential
    (Real.sqrt 8) norm_sqrtPotential_le

/-- The explicit square-root operator squares to the exact Gaussian potential. -/
theorem complexPotentialSqrtOperator_comp_self :
    complexPotentialSqrtOperator.comp complexPotentialSqrtOperator = complexPotentialOperator := by
  ext f
  change complexPotentialSqrtOperator (complexPotentialSqrtOperator f) =ᵐ[volume]
    complexPotentialOperator f
  filter_upwards [coeFn_complexPotentialSqrtOperator (complexPotentialSqrtOperator f),
    coeFn_complexPotentialSqrtOperator f, coeFn_complexPotentialOperator f] with x hsf hf hp
  rw [hsf, hf, hp, ← mul_assoc, ← Complex.ofReal_mul]
  exact congrArg (fun a : ℝ => (a : ℂ) * f x) (Real.mul_self_sqrt (Wlog_pos x).le)

theorem complexPotentialOperator_isPositive : complexPotentialOperator.IsPositive := by
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self complexPotentialSqrtOperator
  have hs := ContinuousLinearMap.isSelfAdjoint_iff'.mp complexPotentialSqrtOperator_isSelfAdjoint
  rw [hs, complexPotentialSqrtOperator_comp_self] at h
  exact h

/-- The potential pairing is the square of the norm of its explicit square-root multiplier. -/
theorem inner_complexPotentialOperator (f : ComplexSturmL2) :
    ⟪f, complexPotentialOperator f⟫_ℂ = (‖complexPotentialSqrtOperator f‖ ^ 2 : ℝ) := by
  calc
    ⟪f, complexPotentialOperator f⟫_ℂ =
        ⟪f, complexPotentialSqrtOperator (complexPotentialSqrtOperator f)⟫_ℂ := by
      rw [← ContinuousLinearMap.comp_apply, complexPotentialSqrtOperator_comp_self]
    _ = ⟪complexPotentialSqrtOperator f, complexPotentialSqrtOperator f⟫_ℂ :=
      (complexPotentialSqrtOperator_isSelfAdjoint.isSymmetric f
        (complexPotentialSqrtOperator f)).symm
    _ = (‖complexPotentialSqrtOperator f‖ ^ 2 : ℝ) := by
      simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rfl

/-- The complex potential pairing equals the same actual weighted Lebesgue integral. -/
theorem inner_complexPotentialOperator_integral (f : ComplexSturmL2) :
    ⟪f, complexPotentialOperator f⟫_ℂ = ((∫ x, Wlog x * ‖f x‖ ^ 2) : ℝ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [coeFn_complexPotentialOperator f] with x hx
  simp only [RCLike.inner_apply, hx, mul_assoc, Complex.mul_conj',
    Complex.ofReal_mul, Complex.ofReal_pow]

theorem norm_complexPotentialSqrtOperator_sq (f : ComplexSturmL2) :
    ‖complexPotentialSqrtOperator f‖ ^ 2 = ∫ x, Wlog x * ‖f x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← inner_complexPotentialOperator, inner_complexPotentialOperator_integral]

/-- Strict positivity of the actual potential prevents its square root from killing a nonzero input. -/
theorem complexPotentialSqrtOperator_eq_zero_iff (f : ComplexSturmL2) :
    complexPotentialSqrtOperator f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have hz := Lp.eq_zero_iff_ae_eq_zero.mp h
    filter_upwards [coeFn_complexPotentialSqrtOperator f, hz] with x hx hzero
    simp only [Pi.zero_apply] at hzero ⊢
    have hs : (sqrtPotential x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (Wlog_pos x)).ne'
    exact (mul_eq_zero.mp (hx.symm.trans hzero)).resolve_left hs
  · rintro rfl
    exact map_zero _

end UnforcedLeray.Sturm
