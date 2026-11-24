import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2

/-!
# Sub `PartII-a_N04_2_2_1`: split of `FlatAdjointSmoothAe`

Source: `the November 2 reference manuscript` lines 1803-1808.
The two conjuncts are independent: smoothness of `v` on `s > 0` (lines 1803-1805) and the
a.e. identification of `v` with `(T0flat).adjoint Z` (lines 1803-1808).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N04_2_2_1


open UnforcedLeray.Short.PartIIa UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226

/-- Smoothness conjunct (source lines 1803-1805). -/
def SmoothProp : Prop :=
  ∀ (ν c σ H1 γs : ℝ), 0 < ν → 0 < σ → σ ≤ H1 → 0 < γs →
    ∀ μ : ℂ, γs ≤ μ.re + 1 / 4 →
      ∀ h : Profile → MeridC, IsFlatLerayRep c σ H1 h →
        ContDiffOn ℝ ∞ (flatAdjointRep ν μ h) {p : Profile | 0 < p.1}

/-- A.e. identification conjunct (source lines 1803-1808). -/
def AeProp : Prop :=
  ∀ (ν c σ H1 γs : ℝ) (hc : 0 < c), 0 < ν → 0 < σ → σ ≤ H1 → 0 < γs →
    ∀ μ : ℂ, γs ≤ μ.re + 1 / 4 →
      ∀ (Z : HSpace c MeridC) (h : Profile → MeridC),
        IsFlatLerayRep c σ H1 h →
        (PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] h →
        ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
          Profile → MeridC) =ᵐ[measureH c] flatAdjointRep ν μ h

theorem flatAdjointSmoothAe_of (hS : SmoothProp) (hAe : AeProp) : FlatAdjointSmoothAe :=
  fun ν c σ H1 γs hc hν hσ hσH1 hγs μ hμ Z h hh hZ =>
    ⟨hS ν c σ H1 γs hν hσ hσH1 hγs μ hμ h hh,
      hAe ν c σ H1 γs hc hν hσ hσH1 hγs μ hμ Z h hh hZ⟩

end UnforcedLeray.Short.PartIIa.N04_2_2_1
