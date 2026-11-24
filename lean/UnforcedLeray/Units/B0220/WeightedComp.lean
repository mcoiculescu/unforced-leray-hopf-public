import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# B0220 helper: weighted composition isometries of `L²`

Blueprint unit B0220 (label `eq:st18-t00113`), `paper/main.tex` lines 3279–3314.

Both maps of the unit, the multiplication `M_s g = s g : H_g → H` (tex line 3309) and the
rescaled lift `J_ε : H → L²(dx dτ)` (tex lines 3310–3311), have the form
`f ↦ (x ↦ L x (f (T x)))` where `‖L x v‖ = ρ x ‖v‖` and `T` pushes `ρ² μ` forward to `ν`.
This file proves once that every such map is a linear isometry `L²(ν; E) → L²(μ; F)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.B0220

/-- A weighted composition: `T : α → β`, pointwise linear maps `L x : E → F` with
`‖L x v‖ = ρ x ‖v‖`, and `T_*(ρ² μ) = ν`. -/
structure WeightedComp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] where
  /-- The change of variables. -/
  T : α → β
  /-- The pointwise linear maps. -/
  L : α → E →ₗ[ℝ] F
  /-- The conformal factor. -/
  ρ : α → ℝ
  measurable_T : Measurable T
  measurable_ρ : Measurable ρ
  measurable_L : Measurable fun p : α × E => L p.1 p.2
  nonneg_ρ : ∀ x, 0 ≤ ρ x
  norm_L : ∀ x v, ‖L x v‖ = ρ x * ‖v‖
  map_eq : (μ.withDensity fun x => ENNReal.ofReal (ρ x ^ 2)).map T = ν

namespace WeightedComp

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

variable (W : WeightedComp μ ν E F)

theorem measurable_density : Measurable fun x => ENNReal.ofReal (W.ρ x ^ 2) :=
  ENNReal.measurable_ofReal.comp (W.measurable_ρ.pow_const 2)

theorem L_eq_zero {x : α} (hx : W.ρ x = 0) (v : E) : W.L x v = 0 := by
  have := W.norm_L x v
  rw [hx, zero_mul] at this
  exact norm_eq_zero.1 this

/-- A `ν`-a.e. property holds at `T x` for `μ`-a.e. `x` with `ρ x ≠ 0`. -/
theorem ae_comp {P : β → Prop} (hP : ∀ᵐ p ∂ν, P p) : ∀ᵐ x ∂μ, W.ρ x ≠ 0 → P (W.T x) := by
  rw [← W.map_eq] at hP
  have h1 := ae_of_ae_map W.measurable_T.aemeasurable hP
  rw [ae_withDensity_iff W.measurable_density] at h1
  filter_upwards [h1] with x hx hρ
  apply hx
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

/-- The pointwise weighted composition of a function. -/
def compFun (f : β → E) (x : α) : F := W.L x (f (W.T x))

theorem compFun_congr {f g : β → E} (h : f =ᵐ[ν] g) : W.compFun f =ᵐ[μ] W.compFun g := by
  filter_upwards [W.ae_comp h] with x hx
  by_cases hρ : W.ρ x = 0
  · simp [compFun, W.L_eq_zero hρ]
  · simp [compFun, hx hρ]

theorem measurable_compFun {f : β → E} (hf : Measurable f) : Measurable (W.compFun f) :=
  W.measurable_L.comp (measurable_id.prodMk (hf.comp W.measurable_T))

/-- The transfer of integrals: `∫ ρ² h(T x) dμ = ∫ h dν`. -/
theorem lintegral_comp {h : β → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, ENNReal.ofReal (W.ρ x ^ 2) * h (W.T x) ∂μ = ∫⁻ p, h p ∂ν := by
  have e := W.map_eq
  calc ∫⁻ x, ENNReal.ofReal (W.ρ x ^ 2) * h (W.T x) ∂μ
      = ∫⁻ p, h p ∂((μ.withDensity fun x => ENNReal.ofReal (W.ρ x ^ 2)).map W.T) := by
        rw [lintegral_map hh W.measurable_T]
        exact (lintegral_withDensity_eq_lintegral_mul _
          W.measurable_density (hh.comp W.measurable_T)).symm
    _ = ∫⁻ p, h p ∂ν := by rw [e]

theorem enorm_L_rpow (x : α) (v : E) :
    ‖W.L x v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (W.ρ x ^ 2) * ‖v‖ₑ ^ (2 : ℝ) := by
  rw [← ofReal_norm, W.norm_L, ENNReal.ofReal_mul (W.nonneg_ρ x), ofReal_norm,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_rpow_of_nonneg (W.nonneg_ρ x) (by norm_num), Real.rpow_two]

theorem eLpNorm_compFun {f : β → E} (hf : Measurable f) :
    eLpNorm (W.compFun f) 2 μ = eLpNorm f 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  simp only [ENNReal.toReal_ofNat, compFun, enorm_L_rpow]
  exact W.lintegral_comp ((hf.enorm).pow_const _)

theorem memLp_compFun {f : β → E} (hf : Measurable f) (hfL : MemLp f 2 ν) :
    MemLp (W.compFun f) 2 μ :=
  ⟨(W.measurable_compFun hf).aestronglyMeasurable, by
    rw [W.eLpNorm_compFun hf]; exact hfL.2⟩

theorem memLp_compFun_Lp (f : Lp E 2 ν) : MemLp (W.compFun f) 2 μ :=
  W.memLp_compFun (Lp.stronglyMeasurable f).measurable (Lp.memLp f)

/-- The weighted composition as a linear isometry `L²(ν; E) → L²(μ; F)`. -/
def toLI : Lp E 2 ν →ₗᵢ[ℝ] Lp F 2 μ where
  toFun f := (W.memLp_compFun_Lp f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [W.compFun_congr (Lp.coeFn_add f g)] with x hx
    rw [hx]
    simp [compFun]
  map_smul' r f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [W.compFun_congr (Lp.coeFn_smul r f)] with x hx
    rw [hx]
    simp [compFun]
  norm_map' f := by
    change ‖(W.memLp_compFun_Lp f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, W.eLpNorm_compFun (Lp.stronglyMeasurable f).measurable, Lp.norm_def]

theorem coeFn_toLI (f : Lp E 2 ν) : W.toLI f =ᵐ[μ] W.compFun f :=
  MemLp.coeFn_toLp (W.memLp_compFun_Lp f)

/-- On a function given pointwise, the isometry is the pointwise weighted composition. -/
theorem coeFn_toLI_toLp {f : β → E} (hfL : MemLp f 2 ν) :
    W.toLI (hfL.toLp f) =ᵐ[μ] W.compFun f :=
  (W.coeFn_toLI _).trans (W.compFun_congr (MemLp.coeFn_toLp hfL))

end WeightedComp

end UnforcedLeray.B0220
