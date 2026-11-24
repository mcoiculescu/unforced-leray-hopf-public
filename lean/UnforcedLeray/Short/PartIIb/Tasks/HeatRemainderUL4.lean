import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder

/-!
# `PartII-b:B3/1`: `D^jU ∈ C_per L⁴` for `j ≤ 2` at the contraction-ball states (SP 2607-2610)

Source of record: `the November 2 reference manuscript`, lines 2607-2610:
"The inverse-distance bounds and the all-age expansion give `D^jV ∈ C_per L⁴`.  For `w`,
interpolation between its `C_per L^p` derivatives and their uniform supremum bounds gives
`D^jw ∈ C_per L⁴`.  Therefore `D^jU ∈ C_per L⁴` for `j ≤ 2`".

The all-order statement `StrongAllOrders` (`PartII-b:S2`, SP 2541-2562: "This proves all spatial
orders ... the resulting `C_τ W^{k,4}` regularity") already carries, at every state `z` of the
contraction ball and every derivative order `k`, a bound of `D^k U(τ)` in `L⁴(ℝ³)` uniform in the
phase (`U = bgField p z = V + w`, the `V`-part from the inverse-distance bounds and the all-age
expansion, the `w`-part by interpolation, exactly as in SP 2607-2610).  Its quantifiers are those
of `B3Stmt.AtBallStates`.  `B3Stmt.UL4` is its orders `k = 0, 1, 2`, with
`‖D⁰U(y)‖ = ‖U(y)‖` (`norm_iteratedFDeriv_zero`) and `‖D¹U(y)‖ = ‖DU(y)‖`
(`norm_iteratedFDeriv_one`).

Main result: `ballHeatRemainder_UL4_of (hS2 : StrongAllOrders) : B3Stmt.AtBallStates B3Stmt.UL4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace B3UL4Aux

/-- From uniform `L⁴` bounds of `D^k F(τ)` for `k = 0, 1, 2` (iterated-derivative form) to the
form of `B3Stmt.UL4` (value, `fderiv`, second iterated derivative). -/
theorem ul4_of_iterated (F : ℝ → SpatialField) (M₀ M₁ M₂ : ℝ)
    (h₀ : ∀ τ, eLpNorm (fun y => iteratedFDeriv ℝ 0 (F τ) y) 4 volume ≤ ENNReal.ofReal M₀)
    (h₁ : ∀ τ, eLpNorm (fun y => iteratedFDeriv ℝ 1 (F τ) y) 4 volume ≤ ENNReal.ofReal M₁)
    (h₂ : ∀ τ, eLpNorm (fun y => iteratedFDeriv ℝ 2 (F τ) y) 4 volume ≤ ENNReal.ofReal M₂) :
    ∃ C : ℝ, ∀ τ : ℝ,
      eLpNorm (F τ) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => fderiv ℝ (F τ) y) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => iteratedFDeriv ℝ 2 (F τ) y) 4 volume ≤ ENNReal.ofReal C := by
  set C : ℝ := max M₀ (max M₁ M₂) with hC
  have e₀ : ENNReal.ofReal M₀ ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have e₁ : ENNReal.ofReal M₁ ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
  have e₂ : ENNReal.ofReal M₂ ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, fun τ => ⟨?_, ?_, (h₂ τ).trans e₂⟩⟩
  · have hn : eLpNorm (F τ) 4 volume =
        eLpNorm (fun y => iteratedFDeriv ℝ 0 (F τ) y) 4 volume :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun y => norm_iteratedFDeriv_zero.symm)
    rw [hn]
    exact (h₀ τ).trans e₀
  · have hn : eLpNorm (fun y => fderiv ℝ (F τ) y) 4 volume =
        eLpNorm (fun y => iteratedFDeriv ℝ 1 (F τ) y) 4 volume :=
      eLpNorm_congr_norm_ae
        (Filter.Eventually.of_forall fun y => (norm_iteratedFDeriv_one (F τ)).symm)
    rw [hn]
    exact (h₁ τ).trans e₁

end B3UL4Aux

/-- **`PartII-b:B3/1` from `StrongAllOrders`** (SP 2607-2610 with SP 2541-2562): at every state
`z` of the contraction ball, `U = bgField p z` has `U(τ)`, `DU(τ)`, `D²U(τ)` bounded in `L⁴(ℝ³)`
uniformly in the phase.  These are the orders `k ≤ 2` of the `C_τ W^{k,4}` bound of
`StrongAllOrders` (`PartII-b:S2`), whose quantifiers are those of `B3Stmt.AtBallStates`. -/
theorem ballHeatRemainder_UL4_of (hS2 : StrongAllOrders) :
    B3Stmt.AtBallStates B3Stmt.UL4 := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, H⟩ := hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, fun p d hreg hν hS hq' z hz hzn => ?_⟩
  obtain ⟨-, hslice, -, -⟩ := H p d hreg hν hS hq' z hz hzn
  obtain ⟨M₀, hM₀⟩ := hslice 0
  obtain ⟨M₁, hM₁⟩ := hslice 1
  obtain ⟨M₂, hM₂⟩ := hslice 2
  exact B3UL4Aux.ul4_of_iterated (bgField p z) M₀ M₁ M₂ (fun τ => (hM₀ τ).2.2)
    (fun τ => (hM₁ τ).2.2) (fun τ => (hM₂ τ).2.2)

/-- Unconditional `PartII-b:B3/1`: `ballHeatRemainder_UL4_of` instantiated with the accepted
`StrongAllOrders` proof (`PartII-b:S2`). -/
theorem ballHeatRemainder_UL4 :
    UnforcedLeray.Short.IIb.B3Stmt.AtBallStates UnforcedLeray.Short.IIb.B3Stmt.UL4 :=
  let h4 := affineInletFacts_proof
  let hQ1 := quadBound_of h4
  let hS1 := _root_.strongFirstDerivative_of h4 hQ1
  let hS2 := strongAllOrders_of h4 hQ1 hS1
  ballHeatRemainder_UL4_of hS2

end UnforcedLeray.Short.IIb
