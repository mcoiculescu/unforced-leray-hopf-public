import UnforcedLeray.Short.PartIIa.Calc.BaseJets
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.FluctProfileSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff

/-!
# Part II-a, base jets: fluctuation and pressure words (`FluctWords`)

Target: `UnforcedLeray.Short.PartIIa.Jet.fluctWords_of : FluctWords` (`Calc/BaseJets.lean`).

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation` for the stream fluctuation `ψ̃ = ψ - S` and the pressure `p` in the decaying gauge).

Smoothness of `ψ̃` and `p` for `s > 0` comes from `LateProfileSmooth` and `HmeanContDiff`
(`fluctProfileSmooth_of`). Each word `K^ℓ ∂_η^a ∂_q^b` is exponentially small, by
`LateFluctuationProfile` (the first and second conjuncts give `ψ̃` and `p`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain)

/-- **Fluctuation and pressure words**: from `LateIngredients` (`fluctWords_of`). -/
theorem fluctWords_of (h : LateIngredients) : FluctWords := by
  unfold FluctWords
  refine ⟨?_, ?_⟩
  · unfold WordsE
    refine ⟨?_, fun ℓ a b => ?_⟩
    · exact UnforcedLeray.Short.PartIIa.fluctProfileSmooth_of h.smooth
        UnforcedLeray.Short.PartI.hmeanContDiff
    · unfold WE
      intro ρ m hρ
      obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := h.fluct ρ m a b ℓ hρ
      exact ⟨C, N, κ, ν₀, hκ, hν₀, fun ν hν hνle tr htr x hx => (H ν hν hνle tr htr x hx).1⟩
  · unfold WordsE
    refine ⟨fun ν c hν hc tr htr => (h.smooth ν c hν hc tr htr).2, fun ℓ a b => ?_⟩
    unfold WE
    intro ρ m hρ
    obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := h.fluct ρ m a b ℓ hρ
    exact ⟨C, N, κ, ν₀, hκ, hν₀, fun ν hν hνle tr htr x hx => (H ν hν hνle tr htr x hx).2⟩

end UnforcedLeray.Short.PartIIa.Jet
