import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.ProductTest
import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.HeatEquation
import UnforcedLeray.Loc.Hyp.H2EmbedsC0

/-!
# H-BgStrong: the background equation at every phase (`BackgroundStrongForm`)

Target: `UnforcedLeray.Blueprint.L13.BackgroundStrongForm` (`Loc/L13PhysicalRemainder.lean`,
line 70), the pointwise-in-time form of `loc:eq:background`, `paper/main.tex` lines 159–168
(blueprint units B0707 heat profile, B0708 background equation), with the coefficient facts
of lines 275–281 (B0710, B0711).

## Main declarations

* `backgroundStrongForm : L13.BackgroundStrongForm` (unconditional);
* `backgroundStrongForm_of_heat`: the reduction to `H2EmbedsC0` and three facts about the heat
  profile `H = H_h[u_dss]` alone (`HeatProfileC0`, `HeatProfileGradientL2`,
  `HeatProfileEquation`), and `backgroundStrongForm_of` (with `HeatProfileRegularity` in
  place of `HeatProfileC0`).


proof of the named hypothesis of `Loc/L01Coefficient.lean`); `heatProfileC0`,
`heatProfileGradientL2` (helpers `GradientL2.lean`, on the compiled heat-smoothing estimates of
`Loc/Hyp/HeatProfileRegularity/Scaling.lean` and `Smoothing.lean`) and `heatProfileEquation`
(helpers `TestSmoothing.lean`, `HeatPairing.lean`, `HeatEquation.lean`).

## Proof

* `N_bg` (helpers `Convection.lean`): `U_*(τ) = H(τ) + r_heat(τ)` is bounded (`C₀`
  representative `V_H + E r_heat`) with weak gradient `∇H + ∇r_heat ∈ L²`, and the columns of
  `U_* ⊗ U_*` are in `L²` (`Ustar_equation.tensor_memL2`). A localized weak product rule puts
  each column `U_j U` in `H¹`, and `N_bg(τ) = -𝔓 ∑_j ∂_j(U_j U)(τ)` satisfies the literal
  `IsMinusLerayDiv`. In Hölder form `N_bg(τ) = -𝔓 ∑_j (P_j(∂_jU, U) + P_j(U, ∂_jU))`, a
  continuous function of `(V(τ), ∇U(τ)) ∈ L^∞ × L²`, hence continuous in `τ`.
* The equation (helpers `ProductTest.lean`): `Ustar_equation` tested with `θ(τ)φ(y)`, Fubini,
  `HeatProfileEquation` and an integration by parts in `τ` give `∫θ'⟨r,φ⟩ = -∫θ g` with the
  continuous `g(τ) = ⟨hΔr + N_bg, φ⟩ - ⟨r, φ⟩ - ½⟨r, (y·∇)φ⟩`; du Bois-Reymond
  (`Lib/BochnerTime`) gives the derivative at every phase.
* `HeatProfileEquation` (helpers `HeatEquation.lean`): `∫⟨H(τ), φ⟩ = e^{-τ}∫⟨u(w),
  (e^{hΔ}φ)(e^{-τ/2}w)⟩ dw`, differentiated under the integral sign, with the commutator
  `y·∇e^{hΔ} = e^{hΔ}(y·∇ - 2hΔ)`.


-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.HypBg

open SobolevGraph

/-- **`BackgroundStrongForm`, conditional form** (lines 159–168, B0707, B0708). For every
unstable background, `N_bg = -𝔓div(U_* ⊗ U_*)` is a continuous `L²` path and
`∂_τ r_heat = hΔr_heat + ½r_heat + ½y·∇r_heat + N_bg` weakly in space at every phase, from
`H² ⊂ C₀`, the `C₀` part of `HeatProfileRegularity`, the `L²` gradient of the heat profile
and its equation. -/
theorem backgroundStrongForm_of_heat (hE : H2EmbedsC0) (hH : HeatProfileC0)
    (hG : HeatProfileGradientL2) (hEq : HeatProfileEquation) : L13.BackgroundStrongForm := by
  intro D hD
  have hB := hD.1
  obtain ⟨E, hErep⟩ := L01.exists_h2ToC0 hE
  obtain ⟨VH, hVc, hVrep⟩ :=
    hH D.h D.period D.udss hB.h_pos hB.period_pos hB.udss_smooth hB.udss_dss hB.udss_bounds
  obtain ⟨W, hWcont, hWweak⟩ :=
    hG D.h D.period D.udss hB.h_pos hB.period_pos hB.udss_smooth hB.udss_dss hB.udss_bounds
  have hr := hB.rheat_continuous
  -- the bounded representative of `U_*`
  have hVU : ∀ τ, ((VH τ + E (D.rheat τ) : ZeroAtInftyContinuousMap Space Space) :
      SpatialField) =ᵐ[volume] D.Ustar τ := by
    intro τ
    refine EventuallyEq.trans ?_ (hB.Ustar_decomposition τ).symm
    filter_upwards [hVrep τ, hErep (D.rheat τ)] with x h1 h2
    simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, h1, h2]
  have hU8 : ∀ τ, MemLp (D.Ustar τ) ∞ volume := fun τ =>
    (L01.c0_memLp_top (VH τ + E (D.rheat τ))).ae_eq (hVU τ)
  -- the weak gradient of `U_*`
  have hdU : ∀ τ k, HasWeakSpatialDerivative k (D.Ustar τ)
      ((W τ k + (D.rheat τ).first k : L2Space) : SpatialField) := by
    intro τ k
    refine ((hWweak τ k).add ((D.rheat τ).hasWeakFirst k)).congr ?_
      (Lp.coeFn_add (W τ k) ((D.rheat τ).first k)).symm
    refine EventuallyEq.trans ?_ (hB.Ustar_decomposition τ).symm
    exact Eventually.of_forall fun x => rfl
  have hdUc : Continuous fun τ => fun k => (W τ k + (D.rheat τ).first k : L2Space) :=
    continuous_pi fun k => ((continuous_apply k).comp hWcont).add
      ((H2.firstCLM k).continuous.comp hr)
  have hcol := hB.Ustar_equation.tensor_memL2
  -- `N_bg = -𝔓 div(U_* ⊗ U_*)`
  have hNeq : (fun τ => convection (hU8 τ) (hdU τ) (hcol τ)) = fun τ =>
      -Leray.projection (convSum (L01.toLinf (VH τ + E (D.rheat τ)))
        (fun k => W τ k + (D.rheat τ).first k)) :=
    funext fun τ => convection_eq (hU8 τ) (hdU τ) (hcol τ) (hVU τ)
  have hNc : Continuous fun τ => convection (hU8 τ) (hdU τ) (hcol τ) := by
    rw [hNeq]
    exact (Leray.projection.continuous.comp (continuous_convSum
      (L01.toLinf.continuous.comp (hVc.add (E.continuous.comp hr))) hdUc)).neg
  refine ⟨fun τ => convection (hU8 τ) (hdU τ) (hcol τ), hNc,
    fun τ => isMinusLerayDiv_convection (hU8 τ) (hdU τ) (hcol τ), ?_⟩
  exact isSimilarityWeakSolution_of_background (H := heatProfile D.h D.udss) (V := VH)
    hB.Ustar_equation hB.Ustar_decomposition hVrep
    (fun φ hφ τ => hEq D.h D.period D.udss hB.h_pos hB.period_pos hB.udss_smooth hB.udss_dss
      hB.udss_bounds φ hφ τ)
    hr hNc (fun τ => isMinusLerayDiv_convection (hU8 τ) (hdU τ) (hcol τ))

/-- The reduction with the named hypothesis `HeatProfileRegularity` (only its `C₀` part is
used). -/
theorem backgroundStrongForm_of (hE : H2EmbedsC0) (hH : HeatProfileRegularity)
    (hG : HeatProfileGradientL2) (hEq : HeatProfileEquation) : L13.BackgroundStrongForm :=
  backgroundStrongForm_of_heat hE (heatProfileC0_of_regularity hH) hG hEq

/-- **`BackgroundStrongForm`** (lines 159–168, B0707, B0708): for every unstable background,
`N_bg = -𝔓div(U_* ⊗ U_*)` is a continuous `L²` path and
`∂_τ r_heat = hΔr_heat + ½r_heat + ½y·∇r_heat + N_bg` weakly in space at every phase. -/
theorem backgroundStrongForm : L13.BackgroundStrongForm :=
  backgroundStrongForm_of_heat h2EmbedsC0 heatProfileC0 heatProfileGradientL2 heatProfileEquation

end UnforcedLeray.Blueprint.HypBg

#print axioms UnforcedLeray.Blueprint.HypBg.backgroundStrongForm
