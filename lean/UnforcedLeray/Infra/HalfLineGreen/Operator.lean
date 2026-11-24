import UnforcedLeray.Infra.HalfLineGreen.Continuity

/-!
# The half-line Green operator as a bounded linear map `𝒳_β → 𝒵_β`

`paper/main.tex`, Section `sec:st18-329`, displays `loc:eq:mixed-inverse` and
`loc:eq:inverse-bound` (lines 422-436):
```
(R_β f)(τ) = ∫_{-∞}^τ K₋(τ,s) f(s) ds - ∫_τ^{τ₀} K₊(τ,s) f(s) ds,
‖R_β f‖_{𝒵_β} ≤ C_β ‖f‖_{𝒳_β}   uniformly in τ₀.
```

`GreenKernel.greenOp K hK hβm hβp τ₀ : WeightedSpace X β τ₀ →L[𝕜] WeightedSpace Z β τ₀` is this
operator, with `greenOp_apply` (the defining formula, the integrand being the continuous
extension `f.extend` of `f`) and `norm_greenOp_le` (`‖R_β‖ ≤ C_β`, where `C_β = K.greenConst β`
does not depend on `τ₀`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Infra.HalfLineGreen

namespace GreenKernel

variable {𝕜 : Type*} [RCLike 𝕜] {X Z : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [NormedSpace ℝ Z] [SMulCommClass ℝ 𝕜 Z]
  (K : GreenKernel 𝕜 X Z)

/-- The Green operator applied to `f ∈ 𝒳_β`, as an element of `𝒵_β`. -/
def greenFun (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp) {τ₀ : ℝ}
    (f : WeightedSpace X β τ₀) : WeightedSpace Z β τ₀ :=
  WeightedSpace.mk (fun τ : Iic τ₀ => K.green τ₀ f.extend τ)
    (K.continuousOn_green hK hβm hβp f.continuous_extend
      (fun _ hs => f.norm_extend_le hs)).domRestrict
    (K.greenConst β * ‖f‖)
    (fun τ => K.norm_green_le hβm hβp τ.2 (fun _ hs => f.norm_extend_le hs))

omit [SMulCommClass ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 Z] in
theorem greenFun_apply (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    {τ₀ : ℝ} (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    K.greenFun hK hβm hβp f τ = K.green τ₀ f.extend τ :=
  WeightedSpace.mk_apply _ _ _ _ τ

/-- The Green operator as a linear map `𝒳_β → 𝒵_β`. -/
def greenLinear (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp) (τ₀ : ℝ) :
    WeightedSpace X β τ₀ →ₗ[𝕜] WeightedSpace Z β τ₀ where
  toFun := K.greenFun hK hβm hβp
  map_add' f g := by
    refine WeightedSpace.ext (fun τ => ?_)
    rw [WeightedSpace.add_apply, greenFun_apply, greenFun_apply, greenFun_apply,
      WeightedSpace.extend_add]
    exact K.green_add hβm τ.2 f.continuous_extend g.continuous_extend
      (fun _ hs => f.norm_extend_le hs) (fun _ hs => g.norm_extend_le hs)
  map_smul' c f := by
    refine WeightedSpace.ext (fun τ => ?_)
    rw [RingHom.id_apply, WeightedSpace.smul_apply, greenFun_apply, greenFun_apply,
      WeightedSpace.extend_smul]
    exact K.green_smul τ₀ c f.extend τ

theorem norm_greenLinear_le (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    (τ₀ : ℝ) (f : WeightedSpace X β τ₀) :
    ‖K.greenLinear hK hβm hβp τ₀ f‖ ≤ K.greenConst β * ‖f‖ := by
  show ‖K.greenFun hK hβm hβp f‖ ≤ _
  unfold greenFun
  exact WeightedSpace.norm_mk_le _ _ _ (mul_nonneg (K.greenConst_nonneg hβm hβp) (norm_nonneg f))

/-- **The half-line Green operator** `R_β : 𝒳_β → 𝒵_β` (`paper/main.tex`,
display `loc:eq:mixed-inverse`), a bounded `𝕜`-linear map. -/
def greenOp (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp) (τ₀ : ℝ) :
    WeightedSpace X β τ₀ →L[𝕜] WeightedSpace Z β τ₀ :=
  (K.greenLinear hK hβm hβp τ₀).mkContinuous (K.greenConst β) (K.norm_greenLinear_le hK hβm hβp τ₀)

/-- The defining formula:
`(R_β f)(τ) = ∫_{-∞}^τ K₋(τ,s) f(s) ds - ∫_τ^{τ₀} K₊(τ,s) f(s) ds`. -/
theorem greenOp_apply (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    {τ₀ : ℝ} (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    K.greenOp hK hβm hβp τ₀ f τ =
      (∫ s in Iio (τ : ℝ), K.Km τ s (f.extend s)) - ∫ s in (τ : ℝ)..τ₀, K.Kp τ s (f.extend s) :=
  K.greenFun_apply hK hβm hβp f τ

/-- **The operator bound** `‖R_β‖ ≤ C_β`, uniformly in the terminal time `τ₀`
(`paper/main.tex`, display `loc:eq:inverse-bound`). -/
theorem norm_greenOp_le (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    (τ₀ : ℝ) : ‖K.greenOp hK hβm hβp τ₀‖ ≤ K.greenConst β :=
  LinearMap.mkContinuous_norm_le _ (K.greenConst_nonneg hβm hβp) _

/-- The pointwise form of the bound: `‖(R_β f)(τ)‖ ≤ C_β ‖f‖ e^{βτ}`. -/
theorem norm_greenOp_apply_le (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β)
    (hβp : β < K.βp) {τ₀ : ℝ} (f : WeightedSpace X β τ₀) (τ : Iic τ₀) :
    ‖K.greenOp hK hβm hβp τ₀ f τ‖ ≤ K.greenConst β * ‖f‖ * Real.exp (β * τ) := by
  rw [greenOp_apply]
  exact K.norm_green_le hβm hβp τ.2 (fun _ hs => f.norm_extend_le hs)

end GreenKernel

end UnforcedLeray.Infra.HalfLineGreen
