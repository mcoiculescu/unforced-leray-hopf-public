import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5`: `PsiBarExists` (the primitive `g` with `g' = -Γ/c`)

Source of record: `the November 2 reference manuscript`, lines 261-288 (zero
circulation). The statement is `PsiBarExists` from `Short/PartI/Sub/T02_5.lean`.

Route. Put `Γ = sliceGamma c w`, which is continuous because it is differentiable (`GammaDeriv`),
and `I = ∫_{(0,∞)} Γ`, which exists because `Γ` is integrable on `(0,∞)` (`GammaIntegrableIoi`).
Take `g(η) = (I - ∫₀^η Γ) / c`.

* `g' = -Γ/c` by the fundamental theorem of calculus.
* `g → 0` at `+∞`, since `∫₀^η Γ → I`.
* `GammaOdd` gives `∫₀^η Γ = ∫₀^{-η} Γ`, so `g(η) → 0` as `η → -∞` as well.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Leaf `PsiBarExists`**: the primitive `g` of `-Γ/c` tending to `0` at both ends, from the
black boxes `GammaDeriv`, `GammaOdd` and `GammaIntegrableIoi`. -/
theorem psiBarExists (h6 : GammaDeriv) (h7 : GammaOdd) (h10 : GammaIntegrableIoi) :
    PsiBarExists := by
  unfold PsiBarExists
  intro c w hs
  -- the circulation profile is continuous, since it is differentiable
  have hcont : Continuous (sliceGamma c w) :=
    continuous_iff_continuousAt.2 fun η => (h6 c w hs η).continuousAt
  -- fundamental theorem of calculus for `u ↦ ∫₀^u Γ`
  have hint : ∀ η : ℝ, HasDerivAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, sliceGamma c w x)
      (sliceGamma c w η) η :=
    fun η => (hcont.integral_hasStrictDerivAt 0 η).hasDerivAt
  -- the limit `I = ∫_{(0,∞)} Γ` at `+∞`
  have hlim : Tendsto (fun u : ℝ => ∫ x in (0 : ℝ)..u, sliceGamma c w x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), sliceGamma c w x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (h10 c w hs) tendsto_id
  -- oddness: `∫₀^η Γ = ∫₀^{-η} Γ`
  have hcomp : ∀ η : ℝ, (∫ x in (0 : ℝ)..η, sliceGamma c w x) =
      ∫ x in (0 : ℝ)..(-η), sliceGamma c w x := by
    intro η
    have hA : (∫ x in (0 : ℝ)..(-η), sliceGamma c w (-x)) =
        ∫ x in η..(0 : ℝ), sliceGamma c w x := by
      rw [intervalIntegral.integral_comp_neg, neg_neg, neg_zero]
    have hB : (∫ x in (0 : ℝ)..(-η), sliceGamma c w (-x)) =
        -∫ x in (0 : ℝ)..(-η), sliceGamma c w x := by
      simp only [h7 c w hs, intervalIntegral.integral_neg]
    have hC : (∫ x in η..(0 : ℝ), sliceGamma c w x) =
        -∫ x in (0 : ℝ)..η, sliceGamma c w x :=
      intervalIntegral.integral_symm 0 η
    linarith
  refine ⟨fun η => ((∫ x in Ioi (0 : ℝ), sliceGamma c w x) -
      ∫ x in (0 : ℝ)..η, sliceGamma c w x) / c, ?_, ?_, ?_⟩
  · -- derivative `-Γ(η)/c`
    intro η
    exact ((hint η).const_sub _).div_const c
  · -- limit at `+∞`
    have h := (hlim.const_sub (∫ x in Ioi (0 : ℝ), sliceGamma c w x)).div_const c
    rw [sub_self, zero_div] at h
    exact h
  · -- limit at `-∞`, through `η ↦ -η`
    have hneg : Tendsto (fun η : ℝ => -η) atBot atTop := Filter.tendsto_neg_atBot_atTop
    have hb : Tendsto (fun η : ℝ => ∫ x in (0 : ℝ)..(-η), sliceGamma c w x) atBot
        (𝓝 (∫ x in Ioi (0 : ℝ), sliceGamma c w x)) := hlim.comp hneg
    have h := (hb.const_sub (∫ x in Ioi (0 : ℝ), sliceGamma c w x)).div_const c
    rw [sub_self, zero_div] at h
    refine h.congr (fun η => ?_)
    rw [hcomp η]

end UnforcedLeray.Short.PartI
