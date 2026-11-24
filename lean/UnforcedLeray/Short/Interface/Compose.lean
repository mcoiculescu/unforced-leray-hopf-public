import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Loc.AssemblyB

/-!
# Interface: `ConstructionClaimShort → MainClaim`

Combination of the leaf Props of `Statements.lean` with the library:

1. `isCoefficients_of_exactBackground`: the proof of the library's `coefficientStep_of`
   (`Loc/L01Coefficient.lean`, lines 175-214) uses only the background half `hD.1` of
   `IsUnstableBackground`; here it is repeated for a record whose background half is known
   (lines 6064-6070 of the shorter proof: `U ∈ C_per C₀`, `∇U ∈ C_per L³`).
2. Leaf 1 (`L3BackgroundOfPath`) turns the coefficient path into the regular background `V`.
3. Leaf 2 (`PeriodicModeEquationToLine`) moves the mode equation from `𝒟'(ℝ³ × ℝ/𝒯ℤ)` to the
   test class of the package; Leaf 3 (`BodyForceL3`) puts the body force in `𝒴₂`
   (`isWeakFreeSolution_of`, draft `Cons/C08PhysicalMode.lean`).
4. Leaves 4a/4b give `Δb_* ∈ 𝒴₂` (`FreeLaplacianRegularity`); then
   `inPeriodicGraph_of_laplacian` gives `𝒯₀b_* ∈ 𝒴₂` and the graph, and
   `solvesModeEquation_of` gives the package form of the mode equation.
5. `Loc.Assembly.mainClaim_of_constructionClaim` closes.

The theorem takes the five leaf Props as the bundle `InterfaceLeaves`; none is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint

open L01 SobolevGraph

/-- `coefficientStep_of` needs only the background half of the package. -/
theorem isCoefficients_of_exactBackground (D : BackgroundData)
    (hB : IsExactBackground D.toBackgroundCore) :
    ∃ c : Coefficients, IsCoefficients D c := by
  obtain ⟨E, hErep⟩ := exists_h2ToC0 h2EmbedsC0
  obtain ⟨VH, WH, YH, hVc, hWc, hYc, hVrep, hWd, hYd⟩ :=
    heatProfileRegularity D.h D.period D.udss hB.h_pos hB.period_pos hB.udss_smooth hB.udss_dss
      hB.udss_bounds
  have hprofile : ∀ τ, heatProfile D.h D.udss (τ + D.period) = heatProfile D.h D.udss τ :=
    fun τ => funext (heatProfile_add_period hB.h_pos hB.udss_dss τ)
  have hVp : Function.Periodic VH D.period := fun τ => by
    have h1 := hVrep (τ + D.period)
    rw [hprofile τ] at h1
    exact C0_eq_of_ae_eq (h1.trans (hVrep τ).symm)
  have hWp : Function.Periodic WH D.period := fun τ => funext fun i => by
    have h1 := hWd (τ + D.period) i
    rw [hprofile τ] at h1
    exact Lp_eq_of_weakDerivative h1 (hWd τ i)
  have hYp : Function.Periodic YH D.period := fun τ => funext fun i => funext fun j => by
    have h1 := hYd (τ + D.period) i j
    rw [hWp τ] at h1
    exact Lp_eq_of_weakDerivative h1 (hYd τ i j)
  have hdec : ∀ τ, heatProfile D.h D.udss τ + ((D.rheat τ).value : SpatialField) =ᵐ[volume]
      D.Ustar τ := fun τ => (hB.Ustar_decomposition τ).symm
  have hV : ∀ τ, ((VH τ + E (D.rheat τ) : ZeroAtInftyContinuousMap Space Space) : SpatialField)
      =ᵐ[volume] D.Ustar τ := by
    intro τ
    refine EventuallyEq.trans ?_ (hdec τ)
    filter_upwards [hVrep τ, hErep (D.rheat τ)] with x h1 h2
    simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, h1, h2]
  have hcons := isConsistentCoef_coefPath (r := D.rheat) hErep hVrep hWd hYd
  exact ⟨_, isCoefficients_of_path D hErep (coefPath E VH WH YH D.rheat)
    (continuous_coefPath hVc hWc hYc hB.rheat_continuous)
    (periodic_coefPath hVp hWp hYp hB.rheat_periodic) hcons
    (fun τ => (coefPath_fst_ae hErep hVrep τ).trans (hdec τ))
    (fun τ => VH τ + E (D.rheat τ)) (hVc.add (E.continuous.comp hB.rheat_continuous))
    (fun τ => by simp only [hVp τ, hB.rheat_periodic τ]) hV⟩

/-- A package record with the given background half and a trivial mode half (used only to read
off the background-dependent clauses of `IsCoefficients`). -/
def dummyData (B : BackgroundCore) : BackgroundData :=
  { toBackgroundCore := B, toModeCore := ⟨0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩ }

end UnforcedLeray.Blueprint

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- The five leaf Props of the bridge (see `Statements.lean`). -/
structure InterfaceLeaves : Prop where
  path : L3BackgroundOfPath
  toLine : PeriodicModeEquationToLine
  bodyForce : BodyForceL3
  window : FreeWindowRegularity
  patch : WindowsToGlobalLaplacian

/-! ## The pairings depend on the background only through a.e. classes -/

theorem symTensorColumns_congr_ae {U U' b : SpatialField} (h : U =ᵐ[volume] U') (j : Fin 3) :
    symTensorColumns U b j =ᵐ[volume] symTensorColumns U' b j := by
  filter_upwards [h] with y hy
  simp only [symTensorColumns, hy]

theorem projectedCoupling_congr {U U' b : ℝ → SpatialField}
    (hUU : ∀ τ, U τ =ᵐ[volume] U' τ) (ψ : SpaceTime → Space) (τ : ℝ) :
    projectedCoupling U b ψ τ = projectedCoupling U' b ψ τ := by
  unfold projectedCoupling lerayDivPairing
  refine congrArg Neg.neg (Finset.sum_congr rfl fun j _ => ?_)
  rw [Infra.JointMeasurableRep.toL2_congr_ae (symTensorColumns_congr_ae (b := b τ) (hUU τ) j)]

theorem solvesPeriodic_congr {h σ P : ℝ} {U U' b : ℝ → SpatialField}
    (hUU : ∀ τ, U τ =ᵐ[volume] U' τ) (hs : SolvesPeriodicModeEquation h σ P U b) :
    SolvesPeriodicModeEquation h σ P U' b := by
  intro φ hφ
  have e : projectedCoupling U b φ = projectedCoupling U' b φ :=
    funext (projectedCoupling_congr hUU φ)
  have := hs φ hφ
  rw [e] at this
  exact this

theorem solvesModeEquation_congr {h σ : ℝ} {U U' b lapB driftB : ℝ → SpatialField}
    (hUU : ∀ τ, U τ =ᵐ[volume] U' τ) (hs : SolvesModeEquation h σ U b lapB driftB) :
    SolvesModeEquation h σ U' b lapB driftB where
  tensor_memL2 := hs.tensor_memL2.mono fun τ hτ j =>
    (hτ j).ae_eq (symTensorColumns_congr_ae (b := b τ) (hUU τ) j)
  value_integrable := hs.value_integrable
  laplacian_integrable := hs.laplacian_integrable
  drift_integrable := hs.drift_integrable
  coupling_integrable := fun ψ hψ => by
    have e : projectedCoupling U b ψ = projectedCoupling U' b ψ :=
      funext (projectedCoupling_congr hUU ψ)
    have := hs.coupling_integrable ψ hψ
    rw [e] at this
    exact this
  identity := fun ψ hψ => by
    have e : projectedCoupling U b ψ = projectedCoupling U' b ψ :=
      funext (projectedCoupling_congr hUU ψ)
    have := hs.identity ψ hψ
    rw [e] at this
    exact this

/-! ## The bridge -/

/-- **`ConstructionClaimShort → ConstructionClaim`**: the energy-class proposition of the shorter
proof gives the graph-mode package of the library, from the five leaves. -/
theorem constructionClaim_of_short (L : InterfaceLeaves) :
    ConstructionClaimShort → ConstructionClaim := by
  rintro ⟨D', hB, hM⟩
  have hP : 0 < D'.period := hB.period_pos
  have hH : IsH1Periodic D'.period D'.bstar := hM.energy
  -- the regular background (lines 6064-6070)
  obtain ⟨c, hc⟩ := isCoefficients_of_exactBackground (dummyData D'.toBackgroundCore) hB
  obtain ⟨V, hVc, hVp, hVU⟩ := hc.Ustar_C0
  obtain ⟨W, hWc, hWp, hWd⟩ := hc.gradient_L3
  obtain ⟨dV, hreg⟩ := L.path D'.period D'.Ustar V W hP hVc hVp hVU hWc hWp hWd
  -- the mode equation on the line
  have hmodeU : SolvesPeriodicModeEquation D'.h D'.σ D'.period (fun τ => (V τ : SpatialField))
      D'.bstar :=
    solvesPeriodic_congr (fun τ => (hVU τ).symm) hM.mode_equation
  have hsol : IsWeakModeSolution D'.h D'.σ (fun τ => (V τ : SpatialField)) D'.bstar :=
    L.toLine D'.h D'.σ D'.period _ dV D'.bstar hP hreg hH hmodeU
  -- the body force and the free equation
  obtain ⟨g, hg, hgae⟩ := L.bodyForce D'.period _ dV D'.bstar hP hreg hH
  have hfree : IsWeakFreeSolution D'.h D'.σ D'.bstar g :=
    isWeakFreeSolution_of hsol (hgae.mono fun τ hτ => hτ.2)
  -- maximal regularity: `Δb_* ∈ 𝒴₂`, then `𝒯₀b_* ∈ 𝒴₂` and the graph
  have hLap : FreeLaplacianRegularity := L.patch L.window
  obtain ⟨lapB, hlap, hL⟩ := hLap D'.h D'.period D'.σ D'.bstar g hB.h_pos hP
    (by linarith [hM.σ_pos]) hH hg hfree
  obtain ⟨driftB, hG⟩ := inPeriodicGraph_of_laplacian hB.h_pos hP hH hg hfree hlap hL
  -- the mode equation in the form of the package
  obtain ⟨C, hC⟩ := hreg.bounded
  have hwL := ae_memLp_slice hP hH.value.periodic hH.value.memL2
  have hline := solvesModeEquation_of hsol hG hreg.continuous hC hwL
  have hstar : SolvesModeEquation D'.h D'.σ D'.Ustar D'.bstar lapB driftB :=
    solvesModeEquation_congr (fun τ => hVU τ) hline
  have hgrow : IsGrowingMode D'.toBackgroundCore
      (⟨D'.σ, D'.bstar, lapB, driftB⟩ : ModeCore) :=
    { graph := hG
      bstar_nonzero := hM.nonzero
      mode_equation := hstar
      bstar_symmetric := hM.symmetric
      σ_pos := hM.σ_pos
      σ_lt := hM.σ_lt }
  exact ⟨_, isUnstableBackground_mk D'.toBackgroundCore ⟨D'.σ, D'.bstar, lapB, driftB⟩ hB hgrow⟩

/-- **The interface theorem**: the energy-class proposition of the shorter proof implies
Theorem A (`MainClaim`), from the five leaves and the compiled localization half. -/
theorem mainClaim_of_constructionClaimShort (L : InterfaceLeaves)
    (hC : ConstructionClaimShort) : MainClaim :=
  Loc.Assembly.mainClaim_of_constructionClaim (constructionClaim_of_short L hC)

end UnforcedLeray.Short.Interface

#print axioms UnforcedLeray.Short.Interface.mainClaim_of_constructionClaimShort
