import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Exponentially weighted spaces of continuous functions on a half-line

`paper/main.tex`, Section `sec:st18-329` (lines 419-421): "Let `𝒳_β` and `𝒵_β` consist of
continuous `X`- and `Z`-valued functions on `(-∞, τ₀]`, with norms
`sup_{τ ≤ τ₀} e^{-βτ} ‖f(τ)‖`."

`WeightedSpace X β τ₀` is this space. It is realised as a type synonym of the Banach space
`Iic τ₀ →ᵇ X` of bounded continuous functions, an element `f` standing for the function
`τ ↦ e^{βτ} • g τ`, where `g = f.toBCF` is the bounded continuous function `τ ↦ e^{-βτ} f τ`.
The norm is therefore the weighted sup norm (`norm_eq_iSup`), the space is complete as soon as
`X` is (`instCompleteSpace`), and the evaluation `f τ` is linear in `f`.

Main API:
* `WeightedSpace.mk u hu C hC`: a continuous `u` with `‖u τ‖ ≤ C e^{βτ}` as an element, with
  `mk_apply` and `norm_mk_le`;
* `norm_apply_le`: `‖f τ‖ ≤ ‖f‖ e^{βτ}`; `norm_le_of_forall`: the converse bound;
* `norm_eq_iSup`: `‖f‖ = ⨆ τ, e^{-βτ} ‖f τ‖`;
* `extend`: the continuous extension `s ↦ f (min τ₀ s)` to the whole line, used as the integrand
  of the Green operator.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real
open scoped BoundedContinuousFunction

namespace UnforcedLeray.Infra.HalfLineGreen

/-- The projection `ℝ → (-∞, b]`, `x ↦ min b x`, is continuous. -/
theorem continuous_projIic (b : ℝ) : Continuous (projIic b : ℝ → Iic b) :=
  (continuous_const.min continuous_id).subtype_mk _

/-- The constant extension `IicExtend f` of a continuous function on `(-∞, b]` is continuous. -/
theorem continuous_IicExtend {β : Type*} [TopologicalSpace β] {b : ℝ} {f : Iic b → β}
    (hf : Continuous f) : Continuous (IicExtend f) :=
  hf.comp (continuous_projIic b)

set_option linter.unusedVariables false in
/-- The exponentially weighted space `𝒳_β` of continuous functions `(-∞, τ₀] → X` with finite
norm `sup_{τ ≤ τ₀} e^{-βτ} ‖f τ‖`. An element is stored as the bounded continuous function
`τ ↦ e^{-βτ} f τ`; see `WeightedSpace.toBCF`. (The weight `β` only enters through the
evaluation `instCoeFun`.) -/
def WeightedSpace (X : Type*) [NormedAddCommGroup X] (β τ₀ : ℝ) : Type _ := Iic τ₀ →ᵇ X

namespace WeightedSpace

variable {X : Type*} [NormedAddCommGroup X] {β τ₀ : ℝ}

instance instNormedAddCommGroup : NormedAddCommGroup (WeightedSpace X β τ₀) :=
  inferInstanceAs (NormedAddCommGroup (Iic τ₀ →ᵇ X))

instance instCompleteSpace [CompleteSpace X] : CompleteSpace (WeightedSpace X β τ₀) :=
  inferInstanceAs (CompleteSpace (Iic τ₀ →ᵇ X))

instance instNormedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] :
    NormedSpace 𝕜 (WeightedSpace X β τ₀) :=
  inferInstanceAs (NormedSpace 𝕜 (Iic τ₀ →ᵇ X))

/-- The rescaled bounded continuous function `τ ↦ e^{-βτ} f τ`. -/
def toBCF (f : WeightedSpace X β τ₀) : Iic τ₀ →ᵇ X := f

/-- An element from its rescaled bounded continuous function. -/
def ofBCF (g : Iic τ₀ →ᵇ X) : WeightedSpace X β τ₀ := g

@[simp] theorem toBCF_ofBCF (g : Iic τ₀ →ᵇ X) : toBCF (ofBCF (β := β) g) = g := rfl

@[simp] theorem ofBCF_toBCF (f : WeightedSpace X β τ₀) : ofBCF (toBCF f) = f := rfl

@[simp] theorem norm_toBCF (f : WeightedSpace X β τ₀) : ‖toBCF f‖ = ‖f‖ := rfl

@[simp] theorem toBCF_add (f g : WeightedSpace X β τ₀) : toBCF (f + g) = toBCF f + toBCF g := rfl

@[simp] theorem toBCF_sub (f g : WeightedSpace X β τ₀) : toBCF (f - g) = toBCF f - toBCF g := rfl

@[simp] theorem toBCF_neg (f : WeightedSpace X β τ₀) : toBCF (-f) = -toBCF f := rfl

@[simp] theorem toBCF_zero : toBCF (0 : WeightedSpace X β τ₀) = 0 := rfl

@[simp] theorem toBCF_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] (c : 𝕜)
    (f : WeightedSpace X β τ₀) : toBCF (c • f) = c • toBCF f := rfl

theorem toBCF_injective : Function.Injective (toBCF : WeightedSpace X β τ₀ → Iic τ₀ →ᵇ X) :=
  fun _ _ h => h

variable [NormedSpace ℝ X]

/-- Evaluation of an element of the weighted space: `f τ = e^{βτ} • (toBCF f) τ`. -/
instance instCoeFun : CoeFun (WeightedSpace X β τ₀) (fun _ => Iic τ₀ → X) :=
  ⟨fun f τ => Real.exp (β * τ) • toBCF f τ⟩

theorem coe_apply (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    f τ = Real.exp (β * τ) • toBCF f τ := rfl

theorem toBCF_apply (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    toBCF f τ = Real.exp (-(β * τ)) • f τ := by
  rw [coe_apply, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

theorem ext {f g : WeightedSpace X β τ₀} (h : ∀ τ, f τ = g τ) : f = g := by
  apply toBCF_injective
  ext τ
  rw [toBCF_apply, toBCF_apply, h]

@[simp] theorem add_apply (f g : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    (f + g) τ = f τ + g τ := by
  simp only [coe_apply, toBCF_add, BoundedContinuousFunction.coe_add, Pi.add_apply, smul_add]

@[simp] theorem sub_apply (f g : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    (f - g) τ = f τ - g τ := by
  simp only [coe_apply, toBCF_sub, BoundedContinuousFunction.coe_sub, Pi.sub_apply, smul_sub]

@[simp] theorem neg_apply (f : WeightedSpace X β τ₀) (τ : Iic τ₀) : (-f) τ = -f τ := by
  simp only [coe_apply, toBCF_neg, BoundedContinuousFunction.coe_neg, Pi.neg_apply, smul_neg]

@[simp] theorem zero_apply (τ : Iic τ₀) : (0 : WeightedSpace X β τ₀) τ = 0 := by
  simp only [toBCF_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    smul_zero]

@[simp] theorem smul_apply {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] [SMulCommClass ℝ 𝕜 X]
    (c : 𝕜) (f : WeightedSpace X β τ₀) (τ : Iic τ₀) : (c • f) τ = c • f τ := by
  simp only [toBCF_smul, BoundedContinuousFunction.coe_smul]
  exact smul_comm _ _ _

/-- Elements of the weighted space are continuous functions on `(-∞, τ₀]`. -/
theorem continuous_coe (f : WeightedSpace X β τ₀) : Continuous (f : Iic τ₀ → X) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val))).smul
    (toBCF f).continuous

/-- The pointwise weighted bound `‖f τ‖ ≤ ‖f‖ e^{βτ}`. -/
theorem norm_apply_le (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    ‖f τ‖ ≤ ‖f‖ * Real.exp (β * τ) := by
  rw [coe_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  exact mul_le_mul_of_nonneg_right ((toBCF f).norm_coe_le_norm τ) (Real.exp_pos _).le

/-- The weighted norm is bounded by any `C ≥ 0` with `‖f τ‖ ≤ C e^{βτ}` for all `τ`. -/
theorem norm_le_of_forall {f : WeightedSpace X β τ₀} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ τ, ‖f τ‖ ≤ C * Real.exp (β * τ)) : ‖f‖ ≤ C := by
  rw [← norm_toBCF, BoundedContinuousFunction.norm_le hC]
  intro τ
  rw [toBCF_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(β * τ)) * ‖f τ‖ ≤ Real.exp (-(β * τ)) * (C * Real.exp (β * τ)) :=
        mul_le_mul_of_nonneg_left (h τ) (Real.exp_pos _).le
    _ = C := by
        rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- The norm of the weighted space is the weighted sup norm `sup_{τ ≤ τ₀} e^{-βτ} ‖f τ‖`. -/
theorem norm_eq_iSup (f : WeightedSpace X β τ₀) :
    ‖f‖ = ⨆ τ : Iic τ₀, Real.exp (-(β * τ)) * ‖f τ‖ := by
  rw [← norm_toBCF, BoundedContinuousFunction.norm_eq_iSup_norm]
  congr 1
  ext τ
  rw [toBCF_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- A continuous function `u` on `(-∞, τ₀]` with `‖u τ‖ ≤ C e^{βτ}` as an element of the
weighted space. -/
def mk (u : Iic τ₀ → X) (hu : Continuous u) (C : ℝ) (hC : ∀ τ, ‖u τ‖ ≤ C * Real.exp (β * τ)) :
    WeightedSpace X β τ₀ :=
  ofBCF (BoundedContinuousFunction.ofNormedAddCommGroup
    (fun τ => Real.exp (-(β * τ)) • u τ)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val).neg).smul hu) C
    (fun τ => by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc Real.exp (-(β * τ)) * ‖u τ‖ ≤ Real.exp (-(β * τ)) * (C * Real.exp (β * τ)) :=
            mul_le_mul_of_nonneg_left (hC τ) (Real.exp_pos _).le
        _ = C := by
            rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]))

@[simp] theorem mk_apply (u : Iic τ₀ → X) (hu : Continuous u) (C : ℝ)
    (hC : ∀ τ, ‖u τ‖ ≤ C * Real.exp (β * τ)) (τ : Iic τ₀) : mk u hu C hC τ = u τ := by
  change Real.exp (β * τ) • (Real.exp (-(β * τ)) • u τ) = u τ
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

theorem norm_mk_le (u : Iic τ₀ → X) (hu : Continuous u) {C : ℝ}
    (hC : ∀ τ, ‖u τ‖ ≤ C * Real.exp (β * τ)) (hC0 : 0 ≤ C) : ‖mk u hu C hC‖ ≤ C :=
  norm_le_of_forall hC0 (fun τ => by rw [mk_apply]; exact hC τ)

/-- The continuous extension `s ↦ f (min τ₀ s)` of an element to the whole line. -/
def extend (f : WeightedSpace X β τ₀) : ℝ → X := IicExtend (f : Iic τ₀ → X)

theorem extend_of_mem (f : WeightedSpace X β τ₀) {s : ℝ} (hs : s ≤ τ₀) :
    f.extend s = f ⟨s, hs⟩ :=
  IicExtend_of_mem _ hs

@[simp] theorem extend_coe (f : WeightedSpace X β τ₀) (τ : Iic τ₀) : f.extend τ = f τ :=
  IicExtend_coe _ τ

theorem continuous_extend (f : WeightedSpace X β τ₀) : Continuous f.extend :=
  continuous_IicExtend f.continuous_coe

theorem norm_extend_le (f : WeightedSpace X β τ₀) {s : ℝ} (hs : s ≤ τ₀) :
    ‖f.extend s‖ ≤ ‖f‖ * Real.exp (β * s) := by
  rw [extend_of_mem f hs]
  exact norm_apply_le f ⟨s, hs⟩

theorem extend_add (f g : WeightedSpace X β τ₀) : (f + g).extend = f.extend + g.extend := by
  ext s
  simp only [extend, IicExtend_apply, add_apply, Pi.add_apply]

theorem extend_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] [SMulCommClass ℝ 𝕜 X]
    (c : 𝕜) (f : WeightedSpace X β τ₀) : (c • f).extend = c • f.extend := by
  ext s
  simp only [extend, IicExtend_apply, smul_apply, Pi.smul_apply]

end WeightedSpace

end UnforcedLeray.Infra.HalfLineGreen
