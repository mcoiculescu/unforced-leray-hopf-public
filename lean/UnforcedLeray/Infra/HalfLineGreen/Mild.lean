import UnforcedLeray.Infra.HalfLineGreen.Operator

/-!
# Mild equation and terminal condition for the half-line Green operator

`paper/main.tex`, Section `sec:st18-329` (lines 400-430): with the evolution `E(τ,s)`, the
dichotomy projections `Π_±` and the backward extension `E₊` on the exterior fibers,
`K₋(τ,s) = E(τ,s) Π₋(s)` and `K₊(τ,s) = E₊(τ,s) Π₊(s)`, and "the evolution law verifies the
mild equation `(∂_τ - 𝓛_*) R_β f = f` and `Π₊(τ₀) (R_β f)(τ₀) = 0`" (lines 429-430).

Abstract setting (`Dichotomy K`): the kernels take values in `Z`, which embeds in `X` through a
bounded map `ι : Z → X` (`H² ↪ H¹` in the manuscript); `E, E₊ : ℝ → ℝ → (X →L X)` and
`Π₊, Π₋ : ℝ → (X →L X)` satisfy
* `ι K₋(τ,s) = E(τ,s) Π₋(s)` (`s < τ`) and `ι K₊(τ,s) = E₊(τ,s) Π₊(s)` (`τ ≤ s`);
* the evolution law `E(τ,r) E(r,s) = E(τ,s)` (`s ≤ r ≤ τ`);
* forward evolution of the exterior extension `E(τ,r) E₊(r,s) Π₊(s) = E₊(τ,s) Π₊(s)` (`r ≤ τ`);
* `E₊ = E` forward on the range of `Π₊`: `E₊(τ,s) Π₊(s) = E(τ,s) Π₊(s)` (`s ≤ τ`);
* `Π₊(s) + Π₋(s) = 1`, `Π₊(s)² = Π₊(s)`;
* intertwining `Π₊(τ) E(τ,s) = E(τ,s) Π₊(s)` (`s ≤ τ`).

Results:
* `Dichotomy.mild`: for `σ ≤ τ ≤ τ₀`,
  `ι (R u)(τ) = E(τ,σ) ι (R u)(σ) + ∫_σ^τ E(τ,s) u(s) ds` (the mild form of
  `(∂_τ - 𝓛_*) R u = u`, in `X`);
* `Dichotomy.terminal`: `Π₊(τ₀) ι (R u)(τ₀) = 0`;
* `Dichotomy.greenOp_mild`, `Dichotomy.greenOp_terminal`: the same for `R_β f`, `f ∈ 𝒳_β`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Infra.HalfLineGreen

open UnforcedLeray.Infra.VolterraEvolution (ae_ne_real)

/-- Splitting a past integral: `∫_{-∞}^τ f = ∫_{-∞}^σ f + ∫_σ^τ f` for `σ ≤ τ`. -/
theorem integral_Iio_eq_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {σ τ : ℝ} (hστ : σ ≤ τ) (hf : IntegrableOn f (Iio τ)) :
    ∫ s in Iio τ, f s = (∫ s in Iio σ, f s) + ∫ s in σ..τ, f s := by
  have hτ' : IntegrableOn f (Iic τ) := (integrableOn_Iic_iff_integrableOn_Iio (f := f)).2 hf
  have hσ' : IntegrableOn f (Iic σ) := hτ'.mono_set (Iic_subset_Iic.2 hστ)
  rw [← integral_Iic_eq_integral_Iio, ← integral_Iic_eq_integral_Iio,
    ← intervalIntegral.integral_Iic_sub_Iic hσ' hτ']
  abel

/-- A function integrable on the past `(-∞, τ)` is interval integrable on `[σ, τ]`. -/
theorem intervalIntegrable_of_integrableOn_Iio {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {σ τ : ℝ} (hστ : σ ≤ τ) (hf : IntegrableOn f (Iio τ)) : IntervalIntegrable f volume σ τ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hστ]
  exact ((integrableOn_Iic_iff_integrableOn_Iio (f := f)).2 hf).mono_set Ioc_subset_Iic_self

variable {𝕜 : Type*} [RCLike 𝕜] {X Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Exponential-dichotomy data realising the kernels of a `GreenKernel` (`paper/main.tex`,
lines 383-414); see the module docstring for the meaning of each field. -/
structure Dichotomy (K : GreenKernel 𝕜 X Z) where
  /-- The continuous embedding `Z → X`. -/
  ι : Z →L[𝕜] X
  /-- The evolution `E(τ,s)` on `X` (used for `s ≤ τ`). -/
  E : ℝ → ℝ → X →L[𝕜] X
  /-- The extension `E₊(τ,s)` on the exterior fibers (used composed with `Π₊(s)`). -/
  Ep : ℝ → ℝ → X →L[𝕜] X
  /-- The exterior projection `Π₊(s)`. -/
  Pp : ℝ → X →L[𝕜] X
  /-- The interior projection `Π₋(s)`. -/
  Pm : ℝ → X →L[𝕜] X
  Km_eq : ∀ τ s, s < τ → ι.comp (K.Km τ s) = (E τ s).comp (Pm s)
  Kp_eq : ∀ τ s, τ ≤ s → ι.comp (K.Kp τ s) = (Ep τ s).comp (Pp s)
  E_comp : ∀ τ r s, s ≤ r → r ≤ τ → (E τ r).comp (E r s) = E τ s
  E_comp_Ep : ∀ τ r s, r ≤ τ → (E τ r).comp ((Ep r s).comp (Pp s)) = (Ep τ s).comp (Pp s)
  Ep_eq : ∀ τ s, s ≤ τ → (Ep τ s).comp (Pp s) = (E τ s).comp (Pp s)
  Pp_add_Pm : ∀ s, Pp s + Pm s = ContinuousLinearMap.id 𝕜 X
  Pp_idem : ∀ s, (Pp s).comp (Pp s) = Pp s
  Pp_comp_E : ∀ τ s, s ≤ τ → (Pp τ).comp (E τ s) = (E τ s).comp (Pp s)

namespace Dichotomy

variable {K : GreenKernel 𝕜 X Z} (D : Dichotomy K)

theorem ι_Km_apply {τ s : ℝ} (hs : s < τ) (x : X) : D.ι (K.Km τ s x) = D.E τ s (D.Pm s x) := by
  have := DFunLike.congr_fun (D.Km_eq τ s hs) x
  simpa only [ContinuousLinearMap.comp_apply] using this

theorem ι_Kp_apply {τ s : ℝ} (hs : τ ≤ s) (x : X) : D.ι (K.Kp τ s x) = D.Ep τ s (D.Pp s x) := by
  have := DFunLike.congr_fun (D.Kp_eq τ s hs) x
  simpa only [ContinuousLinearMap.comp_apply] using this

theorem E_E_apply {τ r s : ℝ} (hsr : s ≤ r) (hrτ : r ≤ τ) (x : X) :
    D.E τ r (D.E r s x) = D.E τ s x := by
  have := DFunLike.congr_fun (D.E_comp τ r s hsr hrτ) x
  simpa only [ContinuousLinearMap.comp_apply] using this

theorem E_Ep_apply {τ r s : ℝ} (hrτ : r ≤ τ) (x : X) :
    D.E τ r (D.Ep r s (D.Pp s x)) = D.Ep τ s (D.Pp s x) := by
  have := DFunLike.congr_fun (D.E_comp_Ep τ r s hrτ) x
  simpa only [ContinuousLinearMap.comp_apply] using this

theorem Ep_apply_eq {τ s : ℝ} (hs : s ≤ τ) (x : X) :
    D.Ep τ s (D.Pp s x) = D.E τ s (D.Pp s x) := by
  have := DFunLike.congr_fun (D.Ep_eq τ s hs) x
  simpa only [ContinuousLinearMap.comp_apply] using this

theorem Pp_add_Pm_apply (s : ℝ) (x : X) : D.Pp s x + D.Pm s x = x := by
  have := DFunLike.congr_fun (D.Pp_add_Pm s) x
  simpa using this

theorem Pp_Pp_apply (s : ℝ) (x : X) : D.Pp s (D.Pp s x) = D.Pp s x := by
  have := DFunLike.congr_fun (D.Pp_idem s) x
  simpa only [ContinuousLinearMap.comp_apply] using this

theorem Pp_Pm_apply (s : ℝ) (x : X) : D.Pp s (D.Pm s x) = 0 := by
  have h : D.Pm s x = x - D.Pp s x := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact D.Pp_add_Pm_apply s x
  rw [h, map_sub, Pp_Pp_apply, sub_self]

theorem Pp_E_apply {τ s : ℝ} (hs : s ≤ τ) (x : X) : D.Pp τ (D.E τ s x) = D.E τ s (D.Pp s x) := by
  have := DFunLike.congr_fun (D.Pp_comp_E τ s hs) x
  simpa only [ContinuousLinearMap.comp_apply] using this

/-- `E(τ,s) = ι K₋(τ,s) + E₊(τ,s) Π₊(s)` for `s < τ`. -/
theorem E_apply_eq_add {τ s : ℝ} (hs : s < τ) (x : X) :
    D.E τ s x = D.ι (K.Km τ s x) + D.Ep τ s (D.Pp s x) := by
  rw [D.ι_Km_apply hs, D.Ep_apply_eq hs.le, ← map_add, add_comm, D.Pp_add_Pm_apply]

/-- Interval integrability of `s ↦ E(τ,s) u(s)` on `[σ, τ]`. -/
theorem intervalIntegrable_E_apply {β : ℝ} (hβm : K.βm < β) {σ τ M : ℝ} (hστ : σ ≤ τ)
    {u : ℝ → X} (hu : Continuous u) (hM : ∀ s < τ, ‖u s‖ ≤ M * Real.exp (β * s)) :
    IntervalIntegrable (fun s => D.E τ s (u s)) volume σ τ := by
  have i1 : IntervalIntegrable (fun s => D.ι (K.Km τ s (u s))) volume σ τ :=
    intervalIntegrable_of_integrableOn_Iio hστ
      (D.ι.integrable_comp (K.integrableOn_Km_apply hβm hu hM))
  have i2 : IntervalIntegrable (fun s => D.Ep τ s (D.Pp s (u s))) volume σ τ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hστ]
    have hc : ContinuousOn (fun s => D.E τ σ (D.ι (K.Kp σ s (u s)))) (Icc σ τ) :=
      ((D.E τ σ).continuous.comp D.ι.continuous).comp_continuousOn
        ((K.continuousOn_Kp_apply hu σ).mono Icc_subset_Ici_self)
    refine hc.congr (fun s hs => ?_)
    simp only
    rw [D.ι_Kp_apply hs.1, D.E_Ep_apply hστ]
  refine (i1.add i2).congr_ae ?_
  rw [uIoc_of_le hστ]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (ae_ne_real τ)] with s hs hsτ
  exact (D.E_apply_eq_add (lt_of_le_of_ne hs.2 hsτ) (u s)).symm

variable [NormedSpace ℝ X] [CompleteSpace X] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- **The mild equation.** For `σ ≤ τ ≤ τ₀`,
`ι (R u)(τ) = E(τ,σ) ι (R u)(σ) + ∫_σ^τ E(τ,s) u(s) ds`. -/
theorem mild {β : ℝ} (hβm : K.βm < β) {τ₀ σ τ M : ℝ} (hστ : σ ≤ τ) (hτ : τ ≤ τ₀) {u : ℝ → X}
    (hu : Continuous u) (hM : ∀ s ≤ τ₀, ‖u s‖ ≤ M * Real.exp (β * s)) :
    D.ι (K.green τ₀ u τ) = D.E τ σ (D.ι (K.green τ₀ u σ)) + ∫ s in σ..τ, D.E τ s (u s) := by
  have hσ₀ : σ ≤ τ₀ := hστ.trans hτ
  -- integrability
  have iτ : IntegrableOn (fun s => K.Km τ s (u s)) (Iio τ) :=
    K.integrableOn_Km_apply hβm hu (fun s hs => hM s (hs.le.trans hτ))
  have iσ : IntegrableOn (fun s => K.Km σ s (u s)) (Iio σ) :=
    K.integrableOn_Km_apply hβm hu (fun s hs => hM s (hs.le.trans hσ₀))
  have jτ : IntervalIntegrable (fun s => K.Kp τ s (u s)) volume τ τ₀ :=
    K.intervalIntegrable_Kp_apply hτ hu
  have jσ : IntervalIntegrable (fun s => K.Kp σ s (u s)) volume σ τ₀ :=
    K.intervalIntegrable_Kp_apply hσ₀ hu
  have iιτ : IntegrableOn (fun s => D.ι (K.Km τ s (u s))) (Iio τ) := D.ι.integrable_comp iτ
  -- the exterior integrand `s ↦ E₊(τ,s) Π₊(s) u(s)` is continuous on `[σ, τ₀]`
  have hcp : ContinuousOn (fun s => D.Ep τ s (D.Pp s (u s))) (Icc σ τ₀) := by
    have hc : ContinuousOn (fun s => D.E τ σ (D.ι (K.Kp σ s (u s)))) (Icc σ τ₀) :=
      ((D.E τ σ).continuous.comp D.ι.continuous).comp_continuousOn
        ((K.continuousOn_Kp_apply hu σ).mono Icc_subset_Ici_self)
    refine hc.congr (fun s hs => ?_)
    simp only
    rw [D.ι_Kp_apply hs.1, D.E_Ep_apply hστ]
  have kστ : IntervalIntegrable (fun s => D.Ep τ s (D.Pp s (u s))) volume σ τ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hστ]
    exact hcp.mono (Icc_subset_Icc_right hτ)
  have kτ₀ : IntervalIntegrable (fun s => D.Ep τ s (D.Pp s (u s))) volume τ τ₀ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ]
    exact hcp.mono (Icc_subset_Icc_left hστ)
  have bστ : IntervalIntegrable (fun s => D.ι (K.Km τ s (u s))) volume σ τ :=
    intervalIntegrable_of_integrableOn_Iio hστ iιτ
  set a := ∫ s in Iio σ, D.ι (K.Km τ s (u s)) with ha
  set b := ∫ s in σ..τ, D.ι (K.Km τ s (u s)) with hb
  set c := ∫ s in σ..τ, D.Ep τ s (D.Pp s (u s)) with hc
  set d := ∫ s in τ..τ₀, D.Ep τ s (D.Pp s (u s)) with hd
  -- (1) the left side
  have h1 : D.ι (K.green τ₀ u τ) = (a + b) - d := by
    rw [GreenKernel.green, map_sub, ← D.ι.integral_comp_comm iτ,
      ← D.ι.intervalIntegral_comp_comm jτ, integral_Iio_eq_add hστ iιτ]
    congr 1
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ] at hs
    exact D.ι_Kp_apply hs.1 (u s)
  -- (2) the propagated value at `σ`
  have h2 : D.E τ σ (D.ι (K.green τ₀ u σ)) = a - (c + d) := by
    rw [GreenKernel.green, map_sub, map_sub, ← D.ι.integral_comp_comm iσ,
      ← D.ι.intervalIntegral_comp_comm jσ, ← (D.E τ σ).integral_comp_comm (D.ι.integrable_comp iσ),
      ← (D.E τ σ).intervalIntegral_comp_comm ⟨D.ι.integrable_comp jσ.1, D.ι.integrable_comp jσ.2⟩,
      intervalIntegral.integral_add_adjacent_intervals kστ kτ₀]
    congr 1
    · refine setIntegral_congr_fun measurableSet_Iio (fun s (hs : s < σ) => ?_)
      rw [D.ι_Km_apply hs, D.E_E_apply hs.le hστ, D.ι_Km_apply (lt_of_lt_of_le hs hστ)]
    · refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le hσ₀] at hs
      rw [D.ι_Kp_apply hs.1, D.E_Ep_apply hστ]
  -- (3) the forcing integral
  have h3 : ∫ s in σ..τ, D.E τ s (u s) = b + c := by
    rw [hb, hc, ← intervalIntegral.integral_add bστ kστ]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real τ] with s hsτ hs
    rw [uIoc_of_le hστ] at hs
    exact D.E_apply_eq_add (lt_of_le_of_ne hs.2 hsτ) (u s)
  rw [h1, h2, h3]
  abel

/-- **The terminal condition** `Π₊(τ₀) ι (R u)(τ₀) = 0`. -/
theorem terminal {τ₀ : ℝ} (u : ℝ → X) : D.Pp τ₀ (D.ι (K.green τ₀ u τ₀)) = 0 := by
  rw [GreenKernel.green, intervalIntegral.integral_same, sub_zero]
  by_cases hint : IntegrableOn (fun s => K.Km τ₀ s (u s)) (Iio τ₀)
  · rw [← D.ι.integral_comp_comm hint, ← (D.Pp τ₀).integral_comp_comm (D.ι.integrable_comp hint)]
    have : ∀ s ∈ Iio τ₀, D.Pp τ₀ (D.ι (K.Km τ₀ s (u s))) = 0 := by
      intro s (hs : s < τ₀)
      rw [D.ι_Km_apply hs, D.Pp_E_apply hs.le, D.Pp_Pm_apply, map_zero]
    rw [setIntegral_congr_fun measurableSet_Iio this, integral_zero]
  · rw [integral_undef hint, map_zero, map_zero]

variable [SMulCommClass ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 Z]

/-- **The mild equation for `R_β f`, `f ∈ 𝒳_β`.** For `σ ≤ τ ≤ τ₀`,
`ι (R_β f)(τ) = E(τ,σ) ι (R_β f)(σ) + ∫_σ^τ E(τ,s) f(s) ds`. -/
theorem greenOp_mild (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    {τ₀ : ℝ} (f : WeightedSpace X β τ₀) {σ τ : Iic τ₀} (hστ : (σ : ℝ) ≤ τ) :
    D.ι (K.greenOp hK hβm hβp τ₀ f τ) =
      D.E τ σ (D.ι (K.greenOp hK hβm hβp τ₀ f σ)) + ∫ s in (σ : ℝ)..τ, D.E τ s (f.extend s) := by
  rw [GreenKernel.greenOp_apply, GreenKernel.greenOp_apply]
  exact D.mild hβm hστ τ.2 f.continuous_extend (fun _ hs => f.norm_extend_le hs)

/-- **The terminal condition for `R_β f`:** `Π₊(τ₀) ι (R_β f)(τ₀) = 0`. -/
theorem greenOp_terminal (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    {τ₀ : ℝ} (f : WeightedSpace X β τ₀) :
    D.Pp τ₀ (D.ι (K.greenOp hK hβm hβp τ₀ f ⟨τ₀, self_mem_Iic⟩)) = 0 := by
  rw [GreenKernel.greenOp_apply]
  exact D.terminal f.extend

end Dichotomy

end UnforcedLeray.Infra.HalfLineGreen
