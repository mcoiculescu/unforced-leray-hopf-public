import UnforcedLeray.Infra.HalfLineGreen.Mild

/-!
# Half-line Green operator in exponentially weighted spaces

Abstract form of `paper/main.tex`, Section `sec:st18-329`, lines 406-436: the right inverse
```
(R_β f)(τ) = ∫_{-∞}^τ E(τ,s) Π₋(s) f(s) ds - ∫_τ^{τ₀} E₊(τ,s) Π₊(s) f(s) ds
```
on the ancient interval `(-∞, τ₀]`, its bound `‖R_β f‖_{𝒵_β} ≤ C_β ‖f‖_{𝒳_β}` uniformly in `τ₀`
(`loc:eq:inverse-bound`), the mild equation and the terminal condition
`Π₊(τ₀) (R_β f)(τ₀) = 0`.

Setting (`𝕜 = ℝ` or `ℂ`, any `RCLike` field): Banach spaces `X`, `Z` and a `GreenKernel 𝕜 X Z`,
i.e. operator kernels `K₋ τ s, K₊ τ s : X →L Z` with
`‖K₋ τ s‖ ≤ C (1 + (τ-s)^{-1/2}) e^{β₋(τ-s)}` (`s < τ`), `‖K₊ τ s‖ ≤ C e^{β₊(τ-s)}` (`τ ≤ s`),
`s ↦ K₋ τ s x` continuous on `(-∞, τ)` and `s ↦ K₊ τ s x` continuous on `[τ, ∞)`.
Fix `β₋ < β < β₊`.

File layout and results:
* `HalfLineGreen/Weighted.lean`: the Banach spaces `𝒳_β = WeightedSpace X β τ₀`,
  `𝒵_β = WeightedSpace Z β τ₀` of continuous functions on `(-∞, τ₀]` with norm
  `sup e^{-βτ} ‖f τ‖` (`WeightedSpace.norm_eq_iSup`, completeness `instCompleteSpace`);
* `HalfLineGreen/Scalar.lean`: the scalar kernel integrals
  `∫_0^∞ (1 + r^{-1/2}) e^{-ar} dr = 1/a + (1/a)^{1/2} Γ(1/2)`, `∫_0^∞ e^{-ar} dr = 1/a`;
* `HalfLineGreen/Kernel.lean`: `GreenKernel`, absolute convergence of both integrals
  (`integrableOn_Km_apply`, `intervalIntegrable_Kp_apply`), the weighted bound
  `‖(R u)(τ)‖ ≤ C_β M e^{βτ}` (`norm_green_le`) with
  `C_β = greenConst β = C (1/(β-β₋) + (1/(β-β₋))^{1/2} Γ(1/2) + 1/(β₊-β))`
  `= C (∫_0^∞ (1+r^{-1/2}) e^{-(β-β₋)r} dr + ∫_0^∞ e^{-(β₊-β)r} dr)` (`greenConst_eq_integral`);
* `HalfLineGreen/Continuity.lean`: under `TimeContinuous` (`τ ↦ K₋(τ,τ-r) x` continuous for
  `r > 0`, `τ ↦ K₊(τ,s) x` continuous on `(-∞,s)`; implied by joint strong continuity,
  `timeContinuous_of_jointly`), `τ ↦ (R u)(τ)` is continuous on `(-∞, τ₀]`
  (`continuousOn_green`);
* `HalfLineGreen/Operator.lean`: `greenOp : 𝒳_β →L[𝕜] 𝒵_β`, `greenOp_apply`,
  `norm_greenOp_le : ‖R_β‖ ≤ C_β` (uniformly in `τ₀`);
* `HalfLineGreen/Mild.lean`: under the algebraic dichotomy hypotheses `Dichotomy K`
  (`ι K₋ = E Π₋`, `ι K₊ = E₊ Π₊`, evolution law, `E E₊ Π₊ = E₊ Π₊` forward, `E₊ Π₊ = E Π₊`
  forward, `Π₊ + Π₋ = 1`, `Π₊² = Π₊`, intertwining), the mild equation
  `ι (R_β f)(τ) = E(τ,σ) ι (R_β f)(σ) + ∫_σ^τ E(τ,s) f(s) ds` (`greenOp_mild`) and the terminal
  condition `Π₊(τ₀) ι (R_β f)(τ₀) = 0` (`greenOp_terminal`);
* this file: the statements for `f ∈ 𝒳_β` collected in `GreenKernel.halfLineGreen` and
  `Dichotomy.halfLineGreen_mild`, and the mild equation with a restricted evolution on `Z`
  (`Dichotomy.mild_restrict`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Infra.HalfLineGreen

variable {𝕜 : Type*} [RCLike 𝕜] {X Z : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [NormedSpace ℝ Z] [SMulCommClass ℝ 𝕜 Z]

namespace GreenKernel

variable (K : GreenKernel 𝕜 X Z)

omit [SMulCommClass ℝ 𝕜 X] [NormedSpace ℝ Z] [SMulCommClass ℝ 𝕜 Z] in
/-- Absolute convergence of the past integral for `f ∈ 𝒳_β`. -/
theorem integrableOn_Km_extend {β : ℝ} (hβm : K.βm < β) {τ₀ : ℝ} (f : WeightedSpace X β τ₀)
    (τ : Iic τ₀) : IntegrableOn (fun s => K.Km τ s (f.extend s)) (Iio (τ : ℝ)) :=
  K.integrableOn_Km_apply hβm f.continuous_extend
    (fun _ hs => f.norm_extend_le (hs.le.trans τ.2))

omit [SMulCommClass ℝ 𝕜 X] [NormedSpace ℝ Z] [SMulCommClass ℝ 𝕜 Z] in
/-- Absolute convergence of the future integral for `f ∈ 𝒳_β`. -/
theorem intervalIntegrable_Kp_extend {β τ₀ : ℝ} (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    IntervalIntegrable (fun s => K.Kp τ s (f.extend s)) volume (τ : ℝ) τ₀ :=
  K.intervalIntegrable_Kp_apply τ.2 f.continuous_extend

/-- **Half-line Green operator, summary.** For `β₋ < β < β₊` and every terminal time `τ₀`,
`R_β = K.greenOp hK hβm hβp τ₀ : 𝒳_β →L[𝕜] 𝒵_β` is given by the absolutely convergent formula
`(R_β f)(τ) = ∫_{-∞}^τ K₋(τ,s) f(s) ds - ∫_τ^{τ₀} K₊(τ,s) f(s) ds`, and
`‖R_β‖ ≤ C_β = C (∫_0^∞ (1+r^{-1/2}) e^{-(β-β₋)r} dr + ∫_0^∞ e^{-(β₊-β)r} dr)`, a constant
independent of `τ₀`. -/
theorem halfLineGreen (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    (τ₀ : ℝ) :
    (∀ (f : WeightedSpace X β τ₀) (τ : Iic τ₀),
      IntegrableOn (fun s => K.Km τ s (f.extend s)) (Iio (τ : ℝ)) ∧
      IntervalIntegrable (fun s => K.Kp τ s (f.extend s)) volume (τ : ℝ) τ₀ ∧
      K.greenOp hK hβm hβp τ₀ f τ =
        (∫ s in Iio (τ : ℝ), K.Km τ s (f.extend s)) - ∫ s in (τ : ℝ)..τ₀, K.Kp τ s (f.extend s)) ∧
    ‖K.greenOp hK hβm hβp τ₀‖ ≤ K.greenConst β ∧
    K.greenConst β = K.C * ((∫ r in Ioi (0 : ℝ), (1 + r ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((β - K.βm) * r))) + ∫ r in Ioi (0 : ℝ), Real.exp (-((K.βp - β) * r))) :=
  ⟨fun f τ => ⟨K.integrableOn_Km_extend hβm f τ, K.intervalIntegrable_Kp_extend f τ,
    K.greenOp_apply hK hβm hβp f τ⟩, K.norm_greenOp_le hK hβm hβp τ₀,
    K.greenConst_eq_integral hβm hβp⟩

end GreenKernel

namespace Dichotomy

variable [CompleteSpace X] [CompleteSpace Z] {K : GreenKernel 𝕜 X Z} (D : Dichotomy K)

/-- **Mild equation and terminal condition, summary.** For `f ∈ 𝒳_β` and
`σ ≤ τ` in `(-∞, τ₀]`: `ι (R_β f)(τ) = E(τ,σ) ι (R_β f)(σ) + ∫_σ^τ E(τ,s) f(s) ds`, the
integrand being interval integrable, and `Π₊(τ₀) ι (R_β f)(τ₀) = 0`. -/
theorem halfLineGreen_mild (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    {τ₀ : ℝ} (f : WeightedSpace X β τ₀) :
    (∀ σ τ : Iic τ₀, (σ : ℝ) ≤ τ →
      IntervalIntegrable (fun s => D.E τ s (f.extend s)) volume (σ : ℝ) τ ∧
      D.ι (K.greenOp hK hβm hβp τ₀ f τ) =
        D.E τ σ (D.ι (K.greenOp hK hβm hβp τ₀ f σ)) + ∫ s in (σ : ℝ)..τ, D.E τ s (f.extend s)) ∧
    D.Pp τ₀ (D.ι (K.greenOp hK hβm hβp τ₀ f ⟨τ₀, self_mem_Iic⟩)) = 0 :=
  ⟨fun _ τ hστ => ⟨D.intervalIntegrable_E_apply hβm hστ f.continuous_extend
      (fun _ hs => f.norm_extend_le (hs.le.trans τ.2)), D.greenOp_mild hK hβm hβp f hστ⟩,
    D.greenOp_terminal hK hβm hβp f⟩

/-- The mild equation with an evolution `E_Z` on `Z` restricting `E`
(`ι E_Z(τ,σ) = E(τ,σ) ι`): `ι ((R_β f)(τ) - E_Z(τ,σ) (R_β f)(σ)) = ∫_σ^τ E(τ,s) f(s) ds`. -/
theorem mild_restrict (EZ : ℝ → ℝ → Z →L[𝕜] Z)
    (hEZ : ∀ τ σ, D.ι.comp (EZ τ σ) = (D.E τ σ).comp D.ι) (hK : K.TimeContinuous) {β : ℝ}
    (hβm : K.βm < β) (hβp : β < K.βp) {τ₀ : ℝ} (f : WeightedSpace X β τ₀) {σ τ : Iic τ₀}
    (hστ : (σ : ℝ) ≤ τ) :
    D.ι (K.greenOp hK hβm hβp τ₀ f τ - EZ τ σ (K.greenOp hK hβm hβp τ₀ f σ)) =
      ∫ s in (σ : ℝ)..τ, D.E τ s (f.extend s) := by
  have h := DFunLike.congr_fun (hEZ τ σ) (K.greenOp hK hβm hβp τ₀ f σ)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [map_sub, h, D.greenOp_mild hK hβm hβp f hστ, add_sub_cancel_left]

end Dichotomy

end UnforcedLeray.Infra.HalfLineGreen
