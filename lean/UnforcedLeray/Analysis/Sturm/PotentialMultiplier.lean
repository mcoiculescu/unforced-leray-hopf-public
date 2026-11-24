import UnforcedLeray.Analysis.Sturm.QuadraticForm
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Actual Gaussian potential multiplication on L²(ℝ)

A measurable bounded real coefficient defines a bounded selfadjoint operator
on the actual Lebesgue L² space. Applying this construction to `Wlog` gives the
potential term of the Gaussian Sturm operator, with operator norm at most 8.
No spectral assertion about the unbounded differential operator is made here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace UnforcedLeray.Sturm
open GaussianPotential

abbrev SturmL2 := Lp ℝ 2 (volume : Measure ℝ)

namespace BoundedMultiplier

variable (w : ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hbound : ∀ x, ‖w x‖ ≤ C)

include hw C hbound

theorem memLp_mul (f : SturmL2) : MemLp (fun x => w x * f x) 2 volume := by
  refine (Lp.memLp f).of_le_mul (c := C) (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

def apply (f : SturmL2) : SturmL2 :=
  (memLp_mul w hw C hbound f).toLp (fun x => w x * f x)

theorem coeFn_apply (f : SturmL2) : apply w hw C hbound f =ᵐ[volume] (fun x => w x * f x) :=
  (memLp_mul w hw C hbound f).coeFn_toLp

def linearMap : SturmL2 →ₗ[ℝ] SturmL2 where
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

theorem norm_apply_le (f : SturmL2) : ‖apply w hw C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_apply w hw C hbound f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

def operator : SturmL2 →L[ℝ] SturmL2 :=
  (linearMap w hw C hbound).mkContinuous C (norm_apply_le w hw C hbound)

theorem coeFn_operator (f : SturmL2) :
    operator w hw C hbound f =ᵐ[volume] (fun x => w x * f x) :=
  coeFn_apply w hw C hbound f

theorem norm_operator_le (hC : 0 ≤ C) : ‖operator w hw C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem operator_isSelfAdjoint : IsSelfAdjoint (operator w hw C hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪operator w hw C hbound f, g⟫_ℝ = ⟪f, operator w hw C hbound g⟫_ℝ
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_operator w hw C hbound f, coeFn_operator w hw C hbound g] with x hf hg
  simp only [Real.inner_apply, hf, hg]
  ring

theorem inner_operator (f : SturmL2) :
    ⟪f, operator w hw C hbound f⟫_ℝ = ∫ x, w x * f x ^ 2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_operator w hw C hbound f] with x hx
  simp only [Real.inner_apply, hx]
  ring

theorem inner_operator_nonneg (hpos : ∀ x, 0 ≤ w x) (f : SturmL2) :
    0 ≤ ⟪f, operator w hw C hbound f⟫_ℝ := by
  rw [inner_operator]
  exact integral_nonneg fun x => mul_nonneg (hpos x) (sq_nonneg _)

end BoundedMultiplier

/-- Multiplication by the manuscript's actual Gaussian log-radius potential. -/
def potentialOperator : SturmL2 →L[ℝ] SturmL2 :=
  BoundedMultiplier.operator Wlog measurable_Wlog 8 norm_Wlog_le_eight

theorem coeFn_potentialOperator (f : SturmL2) :
    potentialOperator f =ᵐ[volume] (fun x => Wlog x * f x) :=
  BoundedMultiplier.coeFn_operator Wlog measurable_Wlog 8 norm_Wlog_le_eight f

theorem norm_potentialOperator_le : ‖potentialOperator‖ ≤ 8 :=
  BoundedMultiplier.norm_operator_le Wlog measurable_Wlog 8 norm_Wlog_le_eight (by norm_num)

theorem potentialOperator_isSelfAdjoint : IsSelfAdjoint potentialOperator :=
  BoundedMultiplier.operator_isSelfAdjoint Wlog measurable_Wlog 8 norm_Wlog_le_eight

theorem inner_potentialOperator (f : SturmL2) :
    ⟪f, potentialOperator f⟫_ℝ = ∫ x, Wlog x * f x ^ 2 :=
  BoundedMultiplier.inner_operator Wlog measurable_Wlog 8 norm_Wlog_le_eight f

theorem inner_potentialOperator_nonneg (f : SturmL2) :
    0 ≤ ⟪f, potentialOperator f⟫_ℝ :=
  BoundedMultiplier.inner_operator_nonneg Wlog measurable_Wlog 8 norm_Wlog_le_eight
    (fun x => (Wlog_pos x).le) f

theorem potentialOperator_isPositive : potentialOperator.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' potentialOperator).mpr
  refine ⟨potentialOperator_isSelfAdjoint, fun f => ?_⟩
  rw [real_inner_comm]
  exact inner_potentialOperator_nonneg f

/-- The actual pointwise positive square root of the Gaussian potential. -/
def sqrtPotential (x : ℝ) : ℝ := Real.sqrt (Wlog x)

theorem measurable_sqrtPotential : Measurable sqrtPotential := measurable_Wlog.sqrt

theorem norm_sqrtPotential_le (x : ℝ) : ‖sqrtPotential x‖ ≤ Real.sqrt 8 := by
  rw [sqrtPotential, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (Wlog_le_eight x)

/-- Multiplication by the explicit square root used in Birman–Schwinger forms. -/
def potentialSqrtOperator : SturmL2 →L[ℝ] SturmL2 :=
  BoundedMultiplier.operator sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le

theorem coeFn_potentialSqrtOperator (f : SturmL2) :
    potentialSqrtOperator f =ᵐ[volume] (fun x => sqrtPotential x * f x) :=
  BoundedMultiplier.coeFn_operator sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le f

theorem norm_potentialSqrtOperator_le : ‖potentialSqrtOperator‖ ≤ Real.sqrt 8 :=
  BoundedMultiplier.norm_operator_le sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le (Real.sqrt_nonneg _)

theorem potentialSqrtOperator_isSelfAdjoint : IsSelfAdjoint potentialSqrtOperator :=
  BoundedMultiplier.operator_isSelfAdjoint sqrtPotential measurable_sqrtPotential (Real.sqrt 8)
    norm_sqrtPotential_le

theorem potentialSqrtOperator_isPositive : potentialSqrtOperator.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' potentialSqrtOperator).mpr
  refine ⟨potentialSqrtOperator_isSelfAdjoint, fun f => ?_⟩
  rw [real_inner_comm]
  exact BoundedMultiplier.inner_operator_nonneg sqrtPotential measurable_sqrtPotential
    (Real.sqrt 8) norm_sqrtPotential_le (fun x => Real.sqrt_nonneg (Wlog x)) f

/-- Squaring the actual multiplier recovers exactly the Gaussian potential operator. -/
theorem potentialSqrtOperator_comp_self :
    potentialSqrtOperator.comp potentialSqrtOperator = potentialOperator := by
  ext f
  change potentialSqrtOperator (potentialSqrtOperator f) =ᵐ[volume] potentialOperator f
  filter_upwards [coeFn_potentialSqrtOperator (potentialSqrtOperator f),
    coeFn_potentialSqrtOperator f, coeFn_potentialOperator f] with x hsf hf hp
  rw [hsf, hf, hp, ← mul_assoc]
  exact congrArg (fun a : ℝ => a * f x) (Real.mul_self_sqrt (Wlog_pos x).le)

/-- The square-root multiplier realizes the potential quadratic form as a squared norm. -/
theorem norm_potentialSqrtOperator_sq (f : SturmL2) :
    ‖potentialSqrtOperator f‖ ^ 2 = ∫ x, Wlog x * f x ^ 2 := by
  calc
    ‖potentialSqrtOperator f‖ ^ 2 = ⟪potentialSqrtOperator f, potentialSqrtOperator f⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ⟪f, potentialSqrtOperator (potentialSqrtOperator f)⟫_ℝ :=
      potentialSqrtOperator_isSelfAdjoint.isSymmetric f (potentialSqrtOperator f)
    _ = ⟪f, potentialOperator f⟫_ℝ := by
      rw [← ContinuousLinearMap.comp_apply, potentialSqrtOperator_comp_self]
    _ = ∫ x, Wlog x * f x ^ 2 := inner_potentialOperator f

end UnforcedLeray.Sturm
