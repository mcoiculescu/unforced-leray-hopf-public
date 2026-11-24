import UnforcedLeray.Units.B0224.FiberSymm
import UnforcedLeray.Units.B0224.Dilation

/-!
# B0224 helper: the limiting semigroup `T_0(t)` and its `H`-adjoint

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379:

  `T_0(t)f(s)   = e^{νs(1-e^{-t})Δ_{q,η}} f(se^{-t})`,
  `T_0(t)^*f(s) = e^{-t/2} e^{νs(e^t-1)Δ_{q,η}} f(se^t)`.

Both are built as `H_θ ∘ D_a` from the age-dependent cylinder heat `H_θ` (`heatH`, self-adjoint
contraction) and the age dilation `D_a` (`dilH`, `‖D_a‖ = a^{1/4}`, `D_a^* = a^{1/2} D_{1/a}`):
`T_0(t) = H_{θ_t} D_{e^{-t}}` with `θ_t(s) = νs(1 - e^{-t})` (`T0`), and
`T_0(t)^* = e^{-t/2} H_{θ_t^*} D_{e^t}` with `θ_t^*(s) = νs(e^t - 1)` (`T0adj`). The pointwise
formulas of the manuscript are `coeFn_T0` and `coeFn_T0adj`. The commutation
`D_a H_θ = H_{θ(a ·)} D_a` (`dilH_comp_heatH`) and `θ_t(e^t s) = θ_t^*(s)` give
`T_0(t)^† = T_0(t)^*` (`adjoint_T0`), and `‖T_0(t)‖, ‖T_0(t)^*‖ ≤ e^{-t/4}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.B0220

/-! ### Heat times -/

/-- The heat time `θ_t(s) = νs(1 - e^{-t})` of `T_0(t)` (tex line 3373). -/
def heatTime (ν t : ℝ) (s : ℝ) : ℝ := ν * s * (1 - Real.exp (-t))

/-- The heat time `θ_t^*(s) = νs(e^t - 1)` of `T_0(t)^*` (tex line 3374). -/
def heatTimeAdj (ν t : ℝ) (s : ℝ) : ℝ := ν * s * (Real.exp t - 1)

theorem measurable_heatTime (ν t : ℝ) : Measurable (heatTime ν t) :=
  (measurable_id.const_mul ν).mul_const _

theorem measurable_heatTimeAdj (ν t : ℝ) : Measurable (heatTimeAdj ν t) :=
  (measurable_id.const_mul ν).mul_const _

theorem heatTime_exp_mul (ν t s : ℝ) : heatTime ν t (Real.exp t * s) = heatTimeAdj ν t s := by
  have h : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold heatTime heatTimeAdj
  linear_combination (-(ν * s)) * h

theorem exp_neg_rpow_quarter (t : ℝ) : Real.exp (-t) ^ (1 / 4 : ℝ) = Real.exp (-t / 4) := by
  rw [← Real.exp_mul]; ring_nf

theorem exp_rpow_quarter (t : ℝ) : Real.exp t ^ (1 / 4 : ℝ) = Real.exp (t / 4) := by
  rw [← Real.exp_mul]; ring_nf

theorem exp_neg_rpow_half (t : ℝ) : Real.exp (-t) ^ (1 / 2 : ℝ) = Real.exp (-t / 2) := by
  rw [← Real.exp_mul]; ring_nf

variable {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Congruence in the parameters -/

theorem heatH_congr (hc : 0 < c) {θ₁ θ₂ : ℝ → ℝ} (h : θ₁ = θ₂) (h₁ : Measurable θ₁)
    (h₂ : Measurable θ₂) :
    (heatH hc h₁ : HSpace c E →L[ℝ] HSpace c E) = heatH hc h₂ := by
  subst h; rfl

theorem dilH_congr {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) :
    (dilH ha : HSpace c E →L[ℝ] HSpace c E) = dilH hb := by
  subst h; rfl

/-- Pointwise: `(D_a H_θ F)(s) = (H_{θ(a ·)} D_a F)(s)`. -/
theorem dil_fiberHeat (a : ℝ) (θ : ℝ → ℝ) (F : Profile → E) :
    dil a (fiberHeat c θ F) = fiberHeat c (fun s => θ (a * s)) (dil a F) := by
  funext p
  simp only [dil, fiberHeat, periodize]

/-- `D_a H_θ = H_{θ(a ·)} D_a`: the heat at age `a s` is the heat at time `θ(a s)`. -/
theorem dilH_comp_heatH (hc : 0 < c) {θ : ℝ → ℝ} (hθ : Measurable θ) {a : ℝ} (ha : 0 < a)
    (hθa : Measurable fun s => θ (a * s)) :
    (dilH ha : HSpace c E →L[ℝ] HSpace c E) ∘L heatH hc hθ = heatH hc hθa ∘L dilH ha := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have hf := Lp.stronglyMeasurable f
  have h1 : (dilH ha (heatH hc hθ f) : Profile → E) =ᵐ[measureH c]
      dil a (heatH hc hθ f : Profile → E) := coeFn_dilH ha _
  have h2 : dil a (heatH hc hθ f : Profile → E) =ᵐ[measureH c]
      dil a (fiberHeat c θ (f : Profile → E)) :=
    dil_congr_ae ha (Lp.stronglyMeasurable _) (stronglyMeasurable_fiberHeat hθ hf)
      (coeFn_heatH hc hθ f)
  have h3 : fiberHeat c (fun s => θ (a * s)) (dil a (f : Profile → E)) =ᵐ[measureH c]
      fiberHeat c (fun s => θ (a * s)) (dilH ha f : Profile → E) :=
    fiberHeat_congr_ae hc hθa (stronglyMeasurable_dil a hf) (Lp.stronglyMeasurable _)
      (coeFn_dilH ha f).symm
  have h4 : (heatH hc hθa (dilH ha f) : Profile → E) =ᵐ[measureH c]
      fiberHeat c (fun s => θ (a * s)) (dilH ha f : Profile → E) := coeFn_heatH hc hθa _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [dil_fiberHeat] at h2
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-! ### The semigroup and its adjoint -/

/-- **The limiting semigroup** `T_0(t)f(s) = e^{νs(1-e^{-t})Δ_{q,η}} f(se^{-t})` on
`H = L²(s^{-3/2} ds dq dη)` (tex line 3373), as `H_{θ_t} ∘ D_{e^{-t}}`. -/
def T0 (hc : 0 < c) (ν t : ℝ) : HSpace c E →L[ℝ] HSpace c E :=
  heatH hc (measurable_heatTime ν t) ∘L dilH (Real.exp_pos (-t))

/-- **The weighted adjoint** `T_0(t)^*f(s) = e^{-t/2} e^{νs(e^t-1)Δ_{q,η}} f(se^t)` (tex line
3374), as `e^{-t/2} H_{θ_t^*} ∘ D_{e^t}`. -/
def T0adj (hc : 0 < c) (ν t : ℝ) : HSpace c E →L[ℝ] HSpace c E :=
  Real.exp (-t / 2) • (heatH hc (measurable_heatTimeAdj ν t) ∘L dilH (Real.exp_pos t))

/-- The manuscript's formula for `T_0(t)` (tex line 3373). -/
theorem coeFn_T0 (hc : 0 < c) (ν t : ℝ) (f : HSpace c E) :
    T0 hc ν t f =ᵐ[measureH c] fun p => planeHeat (ν * p.1 * (1 - Real.exp (-t)))
      (fun z => periodize c (f : Profile → E) (Real.exp (-t) * p.1, z)) p.2 := by
  have hf := Lp.stronglyMeasurable f
  have h0 : T0 hc ν t f = heatH hc (measurable_heatTime ν t) (dilH (Real.exp_pos (-t)) f) := rfl
  have h1 : (heatH hc (measurable_heatTime ν t) (dilH (Real.exp_pos (-t)) f) : Profile → E)
      =ᵐ[measureH c] fiberHeat c (heatTime ν t) (dilH (Real.exp_pos (-t)) f : Profile → E) :=
    coeFn_heatH hc _ _
  have h2 : fiberHeat c (heatTime ν t) (dilH (Real.exp_pos (-t)) f : Profile → E)
      =ᵐ[measureH c] fiberHeat c (heatTime ν t) (dil (Real.exp (-t)) (f : Profile → E)) :=
    fiberHeat_congr_ae hc (measurable_heatTime ν t) (Lp.stronglyMeasurable _)
      (stronglyMeasurable_dil _ hf) (coeFn_dilH _ f)
  rw [h0]
  refine h1.trans (h2.trans (Eventually.of_forall fun p => ?_))
  simp only [fiberHeat, dil, periodize, heatTime]

/-- The manuscript's formula for `T_0(t)^*` (tex line 3374). -/
theorem coeFn_T0adj (hc : 0 < c) (ν t : ℝ) (f : HSpace c E) :
    T0adj hc ν t f =ᵐ[measureH c] fun p => Real.exp (-t / 2) • planeHeat (ν * p.1 * (Real.exp t - 1))
      (fun z => periodize c (f : Profile → E) (Real.exp t * p.1, z)) p.2 := by
  have hf := Lp.stronglyMeasurable f
  have h1 := Lp.coeFn_smul (Real.exp (-t / 2))
    ((heatH hc (measurable_heatTimeAdj ν t) ∘L dilH (Real.exp_pos t)) f)
  refine h1.trans ?_
  have h2a : (heatH hc (measurable_heatTimeAdj ν t) (dilH (Real.exp_pos t) f) : Profile → E)
      =ᵐ[measureH c] fiberHeat c (heatTimeAdj ν t) (dilH (Real.exp_pos t) f : Profile → E) :=
    coeFn_heatH hc _ _
  have h2b : fiberHeat c (heatTimeAdj ν t) (dilH (Real.exp_pos t) f : Profile → E)
      =ᵐ[measureH c] fiberHeat c (heatTimeAdj ν t) (dil (Real.exp t) (f : Profile → E)) :=
    fiberHeat_congr_ae hc (measurable_heatTimeAdj ν t)
      (Lp.stronglyMeasurable _) (stronglyMeasurable_dil _ hf) (coeFn_dilH _ f)
  filter_upwards [h2a, h2b] with p hpa hpb
  rw [Pi.smul_apply, ContinuousLinearMap.comp_apply, hpa, hpb]
  simp only [fiberHeat, dil, periodize, heatTimeAdj]

theorem norm_T0_le (hc : 0 < c) (ν t : ℝ) :
    ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ ≤ Real.exp (-t / 4) := by
  calc ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖
      ≤ ‖(heatH hc (measurable_heatTime ν t) : HSpace c E →L[ℝ] HSpace c E)‖ *
          ‖(dilH (Real.exp_pos (-t)) : HSpace c E →L[ℝ] HSpace c E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.exp (-t) ^ (1 / 4 : ℝ) :=
        mul_le_mul (norm_heatH_le hc _) (norm_dilH_le _) (norm_nonneg _) zero_le_one
    _ = Real.exp (-t / 4) := by rw [one_mul, exp_neg_rpow_quarter]

theorem norm_T0adj_le (hc : 0 < c) (ν t : ℝ) :
    ‖(T0adj hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ ≤ Real.exp (-t / 4) := by
  calc ‖(T0adj hc ν t : HSpace c E →L[ℝ] HSpace c E)‖
      = Real.exp (-t / 2) * ‖(heatH hc (measurable_heatTimeAdj ν t) ∘L dilH (Real.exp_pos t) :
          HSpace c E →L[ℝ] HSpace c E)‖ := by
        rw [T0adj, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (-t / 2) * (1 * Real.exp t ^ (1 / 4 : ℝ)) := by
        gcongr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (norm_heatH_le hc _) (norm_dilH_le _) (norm_nonneg _) zero_le_one)
    _ = Real.exp (-t / 4) := by
        rw [one_mul, exp_rpow_quarter, ← Real.exp_add]; ring_nf

/-- `T_0(0) = 1`: at `t = 0` the heat time vanishes and the dilation is the identity. -/
theorem T0_zero (hc : 0 < c) (ν : ℝ) : (T0 hc ν 0 : HSpace c E →L[ℝ] HSpace c E) = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [coeFn_T0 hc ν 0 f, ae_cell_measureH c] with p hp hcell
  rw [hp]
  change _ = (f : Profile → E) p
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero, one_mul]
  rw [planeHeat_of_nonpos le_rfl]
  exact periodize_of_mem hc _ hcell

section Adjoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **`T_0(t)^*` is the `H`-adjoint of `T_0(t)`** (tex lines 3371–3375), for every `t`. -/
theorem adjoint_T0 (hc : 0 < c) (ν t : ℝ) :
    ContinuousLinearMap.adjoint (T0 hc ν t : HSpace c F →L[ℝ] HSpace c F) = T0adj hc ν t := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have hinv : (Real.exp (-t))⁻¹ = Real.exp t := by rw [Real.exp_neg, inv_inv]
  have hθ : (fun s => heatTime ν t (Real.exp t * s)) = heatTimeAdj ν t :=
    funext fun s => heatTime_exp_mul ν t s
  have e1 : T0adj hc ν t f = Real.exp (-t / 2) •
      heatH hc (measurable_heatTimeAdj ν t) (dilH (Real.exp_pos t) f) := rfl
  have e2 : T0 hc ν t g = heatH hc (measurable_heatTime ν t) (dilH (Real.exp_pos (-t)) g) := rfl
  have e3 : (dilH (Real.exp_pos t) (heatH hc (measurable_heatTime ν t) f) : HSpace c F) =
      heatH hc (measurable_heatTimeAdj ν t) (dilH (Real.exp_pos t) f) := by
    have h := congrArg (fun A : HSpace c F →L[ℝ] HSpace c F => A f)
      (dilH_comp_heatH (E := F) hc (measurable_heatTime ν t) (Real.exp_pos t)
        ((measurable_heatTime ν t).comp (measurable_id.const_mul (Real.exp t))))
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    exact congrArg (fun A : HSpace c F →L[ℝ] HSpace c F => A (dilH (Real.exp_pos t) f))
      (heatH_congr hc hθ _ _)
  rw [e1, e2, real_inner_smul_left]
  calc Real.exp (-t / 2) * ⟪heatH hc (measurable_heatTimeAdj ν t) (dilH (Real.exp_pos t) f), g⟫_ℝ
      = Real.exp (-t) ^ (1 / 2 : ℝ) *
          ⟪g, dilH (Real.exp_pos t) (heatH hc (measurable_heatTime ν t) f)⟫_ℝ := by
        rw [e3, exp_neg_rpow_half, real_inner_comm]
    _ = Real.exp (-t) ^ (1 / 2 : ℝ) *
          ⟪g, dilH (inv_pos.2 (Real.exp_pos (-t))) (heatH hc (measurable_heatTime ν t) f)⟫_ℝ := by
        rw [dilH_congr hinv (inv_pos.2 (Real.exp_pos (-t))) (Real.exp_pos t)]
    _ = ⟪dilH (Real.exp_pos (-t)) g, heatH hc (measurable_heatTime ν t) f⟫_ℝ :=
        (inner_dilH (Real.exp_pos (-t)) g _).symm
    _ = ⟪heatH hc (measurable_heatTime ν t) f, dilH (Real.exp_pos (-t)) g⟫_ℝ := real_inner_comm _ _
    _ = ⟪f, heatH hc (measurable_heatTime ν t) (dilH (Real.exp_pos (-t)) g)⟫_ℝ :=
        inner_heatH hc _ f _

/-- `‖T_0(t)^*‖ = ‖T_0(t)‖`. -/
theorem norm_T0adj_eq_norm_T0 (hc : 0 < c) (ν t : ℝ) :
    ‖(T0adj hc ν t : HSpace c F →L[ℝ] HSpace c F)‖ = ‖(T0 hc ν t : HSpace c F →L[ℝ] HSpace c F)‖ := by
  rw [← adjoint_T0, LinearIsometryEquiv.norm_map]

end Adjoint

end UnforcedLeray.B0224
