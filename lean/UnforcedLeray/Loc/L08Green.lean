import UnforcedLeray.Loc.L08Green.Kernel
import UnforcedLeray.Loc.L08Green.ForwardSmoothing

/-!
# Step L8 `GreenStep`: the half-line Green operator (lines 406–428)

`paper/main.tex` lines 406–428 (`loc:eq:mixed-inverse`, `loc:eq:inverse-bound`), blueprint units
B1018, B1019, B1020; the step is `UnforcedLeray.Blueprint.GreenStep`
(`Blueprint/Localization/Linear.lean`, line 327).

For the outputs of L1–L3, L6 and L7 we build
```
(𝓡_β f)(τ) = ∫_{-∞}^τ E_Z(τ,s)Π₋(s) f(s) ds - ∫_τ^{τ₀} E₊(τ,s)Π₊(s) f(s) ds
```
as the operator `UnforcedLeray.Infra.HalfLineGreen.GreenKernel.greenOp` (with `𝕜 = ℝ`) of the
kernels of `L08Green/Kernel.lean`, transported to the blueprint's weighted spaces
`WeightedX τ₀ → WeightedZ τ₀` (the stored weighted coordinates are the same bounded continuous
functions). The mild equation, the terminal condition `Π₊(τ₀)(𝓡_β f)(τ₀) = 0` and the bound
`‖𝓡_β‖ ≤ C_β` uniform in `τ₀` come from `Infra/HalfLineGreen` (`Dichotomy.halfLineGreen_mild`,
`GreenKernel.norm_greenOp_le`); the rates are those of L6, `β₋ < β < β₊`, and the kernel bounds
are `loc:eq:past-bound`, `loc:eq:future-bound` of L7.

Main results:
* `isGreenOperator_of_continuity`: for given data with the hypothesis `hZ`
  (`τ ↦ E_Z(τ,σ) y` is continuous on `(σ, ∞)` in `Z`), the Green family exists;
* `greenFamily_formula`: that family is the formula `loc:eq:mixed-inverse`;
* `greenStep_of`: `ForwardSmoothingContinuity → GreenStep`;
* `forwardSmoothingContinuity`: the hypothesis `ForwardSmoothingContinuity` holds;
* `greenStep : GreenStep`, with no hypotheses.

The `Z`-valued continuity of `τ ↦ (𝓡_β f)(τ)`, required by the manuscript's definition of
`𝒵_β` (line 406, "continuous `Z`-valued functions"), needs continuity of `τ ↦ E_Z(τ,σ) y` in
`H²`, which `IsEvolution` (L3) does not record: it gives `E_Z(τ,s) : X → Z` only through
`ιZ E_Z = E` and the size `C (τ-s)^{-1/2}`. It is proved in `L08Green/ForwardSmoothing.lean`
for every evolution satisfying `IsEvolution`, by identifying `E_Z(τ,σ) = E^Z(τ,r) E_Z(r,σ)`
(`σ < r < τ`) with the strongly continuous `Z`-level Volterra evolution `E^Z` of line 300
(through the infrastructure of `Loc/L03Evolution/{Abstract,Free,ZBound,ZContinuity}.lean`).
Everything else (the continuity of the kernels in `s`, the extension `E₊` of the backward
exterior evolution and its evolution law, the dichotomy algebra) is proved in
`L08Green/Kernel.lean` and `L08Green/Algebra.lean` from L3, L6, L7.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped BoundedContinuousFunction

namespace UnforcedLeray.Blueprint.L08Green

open UnforcedLeray.Blueprint UnforcedLeray.Infra.HalfLineGreen

/-! ## The blueprint's weighted spaces are the spaces of `Infra/HalfLineGreen` -/

/-- `𝒳_β(τ₀)` in the blueprint's coordinates to `WeightedSpace X β τ₀`: the identity on the
stored function `τ ↦ e^{-βτ} f(τ)`. -/
def toWeightedSpace (β τ₀ : ℝ) : WeightedX τ₀ →L[ℝ] WeightedSpace X β τ₀ :=
  LinearMap.mkContinuous
    { toFun := fun F => WeightedSpace.ofBCF (show Iic τ₀ →ᵇ X from F)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun F => le_of_eq (by rw [one_mul]; rfl))

/-- `WeightedSpace Z β τ₀` to `𝒵_β(τ₀)` in the blueprint's coordinates. -/
def ofWeightedSpace (β τ₀ : ℝ) : WeightedSpace Z β τ₀ →L[ℝ] WeightedZ τ₀ :=
  LinearMap.mkContinuous
    { toFun := fun w => (show WeightedZ τ₀ from WeightedSpace.toBCF w)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun w => le_of_eq (by rw [one_mul]; rfl))

theorem norm_toWeightedSpace_apply (β τ₀ : ℝ) (F : WeightedX τ₀) :
    ‖toWeightedSpace β τ₀ F‖ = ‖F‖ := rfl

theorem norm_ofWeightedSpace_apply (β τ₀ : ℝ) (w : WeightedSpace Z β τ₀) :
    ‖ofWeightedSpace β τ₀ w‖ = ‖w‖ := rfl

/-- The blueprint's `unweightX` is the evaluation of `WeightedSpace`, extended. -/
theorem unweightX_eq_extend (β : ℝ) {τ₀ : ℝ} (F : WeightedX τ₀) {r : ℝ} (hr : r ≤ τ₀) :
    unweightX β F r = (toWeightedSpace β τ₀ F).extend r := by
  rw [WeightedSpace.extend_of_mem _ hr]
  simp only [unweightX, hr, ↓reduceDIte]
  rfl

/-! ## The Green family -/

/-- `𝓡_β(τ₀) : 𝒳_β(τ₀) → 𝒵_β(τ₀)` in the blueprint's weighted coordinates. -/
def greenFamily (K : GreenKernel ℝ X Z) (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β)
    (hβp : β < K.βp) : GreenFamily :=
  fun τ₀ => (ofWeightedSpace β τ₀).comp ((K.greenOp hK hβm hβp τ₀).comp (toWeightedSpace β τ₀))

theorem unweight_greenFamily (K : GreenKernel ℝ X Z) (hK : K.TimeContinuous) {β : ℝ}
    (hβm : K.βm < β) (hβp : β < K.βp) {τ₀ : ℝ} (F : WeightedX τ₀) {τ : ℝ} (hτ : τ ≤ τ₀) :
    unweight β (greenFamily K hK hβm hβp τ₀ F) τ =
      K.greenOp hK hβm hβp τ₀ (toWeightedSpace β τ₀ F) ⟨τ, hτ⟩ := by
  rw [unweight_of_le β _ hτ]
  rfl

/-- The family is the formula `loc:eq:mixed-inverse` (lines 410–414):
`(𝓡_β f)(τ) = ∫_{-∞}^τ K₋(τ,s) f(s) ds - ∫_τ^{τ₀} K₊(τ,s) f(s) ds`. -/
theorem greenFamily_formula (K : GreenKernel ℝ X Z) (hK : K.TimeContinuous) {β : ℝ}
    (hβm : K.βm < β) (hβp : β < K.βp) {τ₀ : ℝ} (F : WeightedX τ₀) {τ : ℝ} (hτ : τ ≤ τ₀) :
    unweight β (greenFamily K hK hβm hβp τ₀ F) τ =
      (∫ s in Iio τ, K.Km τ s (unweightX β F s)) -
        ∫ s in τ..τ₀, K.Kp τ s (unweightX β F s) := by
  rw [unweight_greenFamily K hK hβm hβp F hτ, GreenKernel.greenOp_apply]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Iio (fun s (hs : s < τ) => ?_)
    simp only
    rw [unweightX_eq_extend β F (hs.le.trans hτ)]
  · refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ] at hs
    simp only
    rw [unweightX_eq_extend β F hs.2]

theorem norm_greenFamily_le (K : GreenKernel ℝ X Z) (hK : K.TimeContinuous) {β : ℝ}
    (hβm : K.βm < β) (hβp : β < K.βp) (τ₀ : ℝ) :
    ‖greenFamily K hK hβm hβp τ₀‖ ≤ K.greenConst β := by
  refine ContinuousLinearMap.opNorm_le_bound _ (K.greenConst_nonneg hβm hβp) (fun F => ?_)
  change ‖ofWeightedSpace β τ₀ (K.greenOp hK hβm hβp τ₀ (toWeightedSpace β τ₀ F))‖ ≤ _
  rw [norm_ofWeightedSpace_apply, ← norm_toWeightedSpace_apply β τ₀ F]
  exact (K.greenOp hK hβm hβp τ₀).le_of_opNorm_le (K.norm_greenOp_le hK hβm hβp τ₀) _

/-! ## The Green operator of the linearized evolution -/

section Green

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}
  {sp : SpectralSplitting X} {EplusZ : BackwardLift}

/-- **The half-line Green operator** (lines 406–428, B1018–B1020) for given data: under the
continuity hypothesis `hZ` on the smoothing `E_Z`, there is `𝓡_β` with the mild equation, the
terminal condition and the uniform bound of `IsGreenOperator`. -/
theorem isGreenOperator_of_continuity (hP : 0 < D.period) (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ)
    (hZ : ∀ (σ : ℝ) (y : X), ContinuousOn (fun τ => ev.EZ τ σ y) (Ioi σ)) :
    ∃ R : GreenFamily, IsGreenOperator D ev sp R := by
  obtain ⟨C₁, hC₁⟩ := hpp.past_bound
  obtain ⟨C₂, hC₂⟩ := hpp.future_bound
  set K := greenKernel hev hsp hpp hP hC₁ hC₂ with hK_def
  have hK : K.TimeContinuous := timeContinuous hev hsp hpp hP hC₁ hC₂ hZ
  set Dk := dichotomy hev hsp hpp hP hC₁ hC₂ with hDk_def
  have hβm : K.βm < sp.β := hsp.rate_lower
  have hβp : sp.β < K.βp := hsp.rate_upper
  refine ⟨greenFamily K hK hβm hβp, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro τ₀ _ F s τ hsτ hττ₀
    have h : IntervalIntegrable
        (fun r => ev.E τ r ((toWeightedSpace sp.β τ₀ F).extend r)) volume s τ :=
      ((Dk.halfLineGreen_mild hK hβm hβp (toWeightedSpace sp.β τ₀ F)).1
        ⟨s, hsτ.trans hττ₀⟩ ⟨τ, hττ₀⟩ hsτ).1
    refine (((intervalIntegrable_iff_integrableOn_Ioc_of_le hsτ).1 h).mono_set
      Ioo_subset_Ioc_self).congr_fun (fun r hr => ?_) measurableSet_Ioo
    simp only
    rw [unweightX_eq_extend sp.β F (hr.2.le.trans hττ₀)]
  · intro τ₀ _ F s τ hsτ hττ₀
    have h : ιZ (K.greenOp hK hβm hβp τ₀ (toWeightedSpace sp.β τ₀ F) ⟨τ, hττ₀⟩) =
        ev.E τ s (ιZ (K.greenOp hK hβm hβp τ₀ (toWeightedSpace sp.β τ₀ F)
          ⟨s, hsτ.trans hττ₀⟩)) +
          ∫ r in s..τ, ev.E τ r ((toWeightedSpace sp.β τ₀ F).extend r) :=
      ((Dk.halfLineGreen_mild hK hβm hβp (toWeightedSpace sp.β τ₀ F)).1
        ⟨s, hsτ.trans hττ₀⟩ ⟨τ, hττ₀⟩ hsτ).2
    rw [intervalIntegral.integral_of_le hsτ, integral_Ioc_eq_integral_Ioo] at h
    rw [unweight_greenFamily K hK hβm hβp F hττ₀,
      unweight_greenFamily K hK hβm hβp F (hsτ.trans hττ₀), h]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    rw [unweightX_eq_extend sp.β F (hr.2.le.trans hττ₀)]
  · intro τ₀ _ F
    rw [unweight_greenFamily K hK hβm hβp F le_rfl]
    exact (Dk.halfLineGreen_mild hK hβm hβp (toWeightedSpace sp.β τ₀ F)).2
  · exact ⟨K.greenConst sp.β, fun τ₀ _ => norm_greenFamily_le K hK hβm hβp τ₀⟩

end Green

/-! ## The step -/

/-- **Forward smoothing is continuous into `Z = H²_div`** (proved below:
`forwardSmoothingContinuity`). For every
background package and every evolution `E` of L3 (`IsEvolution`), the smoothing
`E_Z(τ,σ) : X → Z` is strongly continuous in the final time: `τ ↦ E_Z(τ,σ) y` is continuous
on `(σ, ∞)` in the `H²` norm, for every `σ` and `y ∈ X`.

* Tex: lines 299–306 (the smoothing `X → Z` of the evolution) and 406 (`𝒵_β` consists of
  *continuous* `Z`-valued functions, so `𝓡_β f ∈ 𝒵_β` needs this); units B0713, B1018, and
  B1020 ("`ℛ_β` maps `𝒳_β` into `𝒵_β` (including continuity in `Z`)").
* `IsEvolution` records the `X`-valued joint strong continuity of `E`, the identity
  `ιZ E_Z = E` and the size `‖E_Z(τ,s)‖ ≤ C(τ-s)^{-1/2}`, but no continuity in the `Z`-norm.
  It is proved from the `Z`-level Volterra problem of line 300 (`S₀|_Z`, `S₀ : X → Z`,
  `𝓑_* : Z → X`), whose evolution is strongly continuous on `Z`
  (`continuousOn_EZ_of_isEvolution`, `L08Green/ForwardSmoothing.lean`). -/
def ForwardSmoothingContinuity : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D →
    ∀ (c : Coefficients) (S : FreeEvolution) (ev : Evolution),
      IsCoefficients D c → IsFreeEvolution D.h S → IsEvolution D c S ev →
        ∀ (σ : ℝ) (y : X), ContinuousOn (fun τ => ev.EZ τ σ y) (Ioi σ)

/-- **Step L8** `GreenStep` (lines 406–428, `loc:eq:mixed-inverse`, `loc:eq:inverse-bound`;
units B1018, B1019, B1020), from the named hypothesis `ForwardSmoothingContinuity`. -/
theorem greenStep_of (h : ForwardSmoothingContinuity) : GreenStep := by
  intro D hD c S ev sp EplusZ hc hS hev hsp hpp
  exact isGreenOperator_of_continuity hD.1.period_pos hev hsp hpp (h D hD c S ev hc hS hev)

/-- `ForwardSmoothingContinuity` holds (lines 299–306, 406; units B0713, B1018, B1020): proved
for every evolution with the characterizations of L1–L3 in `L08Green/ForwardSmoothing.lean`. -/
theorem forwardSmoothingContinuity : ForwardSmoothingContinuity :=
  fun _ hD _ _ _ hc hS hev => continuousOn_EZ_of_isEvolution hD.1.h_pos hD.1.period_pos hc hS hev

/-- **Step L8** `GreenStep` (`paper/main.tex` lines 406–428, `loc:eq:mixed-inverse`,
`loc:eq:inverse-bound`; blueprint units B1018, B1019, B1020): for every unstable background
and the outputs of L1–L3, L6 and L7, the half-line Green operator `𝓡_β(τ₀) : 𝒳_β(τ₀) → 𝒵_β(τ₀)`
exists, is a mild solution operator of `(∂_τ - 𝓛_*) z = f` with `Π₊(τ₀) z(τ₀) = 0`, and is
bounded uniformly in `τ₀ ≤ 0`. No hypotheses. -/
theorem greenStep : GreenStep :=
  greenStep_of forwardSmoothingContinuity

end UnforcedLeray.Blueprint.L08Green
