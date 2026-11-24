import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2

/-!
# Sub `PartII-a_N04_2_2_3`: split of `FlatAdjointGen2Bound`

Source: `the November 2 reference manuscript` lines 1814-1835.
The six second-order terms are bounded in three pairs, each with its own exponent and constant;
the assembly uses `1 ≤ GammaBox`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N04_2_2_3


open UnforcedLeray.Short.PartIIa UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226

/-- Bound for `genDiff2Term1`, `genDiff2Term2` (source lines 1814-1835). -/
def PairA : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < c → 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ h : Profile → MeridC, IsFlatLerayRep c σ H1 h →
          ∃ (ht1 : MemLp (genDiff2Term1 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht2 : MemLp (genDiff2Term2 ν (flatAdjointRep ν μ h)) 2 (measureH c)),
            4 * ‖ht1.toLp (genDiff2Term1 ν (flatAdjointRep ν μ h))‖ +
              4 * ‖ht2.toLp (genDiff2Term2 ν (flatAdjointRep ν μ h))‖ ≤
                C * GammaBox ν c σ H1 L1 M γs ^ k * flatProjMomentNorm c h

/-- Bound for `genDiff2Term3`, `genDiff2Term4`. -/
def PairB : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < c → 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ h : Profile → MeridC, IsFlatLerayRep c σ H1 h →
          ∃ (ht3 : MemLp (genDiff2Term3 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht4 : MemLp (genDiff2Term4 ν (flatAdjointRep ν μ h)) 2 (measureH c)),
            4 * ‖ht3.toLp (genDiff2Term3 ν (flatAdjointRep ν μ h))‖ +
              ‖ht4.toLp (genDiff2Term4 ν (flatAdjointRep ν μ h))‖ ≤
                C * GammaBox ν c σ H1 L1 M γs ^ k * flatProjMomentNorm c h

/-- Bound for `genDiff2Term5`, `genDiff2Term6`. -/
def PairC : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < c → 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ h : Profile → MeridC, IsFlatLerayRep c σ H1 h →
          ∃ (ht5 : MemLp (genDiff2Term5 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht6 : MemLp (genDiff2Term6 ν (flatAdjointRep ν μ h)) 2 (measureH c)),
            3 * ‖ht5.toLp (genDiff2Term5 ν (flatAdjointRep ν μ h))‖ +
              ‖ht6.toLp (genDiff2Term6 ν (flatAdjointRep ν μ h))‖ ≤
                C * GammaBox ν c σ H1 L1 M γs ^ k * flatProjMomentNorm c h

theorem flatAdjointGen2Bound_of (hA : PairA) (hB : PairB) (hC : PairC) :
    FlatAdjointGen2Bound := by
  obtain ⟨ka, Ca, hCa, hA⟩ := hA
  obtain ⟨kb, Cb, hCb, hB⟩ := hB
  obtain ⟨kc, Cc, hCc, hC⟩ := hC
  refine ⟨ka + kb + kc, Ca + Cb + Cc, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  obtain ⟨ht1, ht2, bA⟩ := hA ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  obtain ⟨ht3, ht4, bB⟩ := hB ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  obtain ⟨ht5, ht6, bC⟩ := hC ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  refine ⟨ht1, ht2, ht3, ht4, ht5, ht6, ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ GammaBox ν c σ H1 L1 M γs :=
    one_le_GammaBox hν hc hσ hσH1 hL1 hM0 hγs
  have hF0 : 0 ≤ flatProjMomentNorm c h := flatProjMomentNorm_nonneg c h
  have p1 : GammaBox ν c σ H1 L1 M γs ^ ka ≤ GammaBox ν c σ H1 L1 M γs ^ (ka + kb + kc) :=
    pow_le_pow_right₀ hG1 (by omega)
  have p2 : GammaBox ν c σ H1 L1 M γs ^ kb ≤ GammaBox ν c σ H1 L1 M γs ^ (ka + kb + kc) :=
    pow_le_pow_right₀ hG1 (by omega)
  have p3 : GammaBox ν c σ H1 L1 M γs ^ kc ≤ GammaBox ν c σ H1 L1 M γs ^ (ka + kb + kc) :=
    pow_le_pow_right₀ hG1 (by omega)
  have l1 : Ca * GammaBox ν c σ H1 L1 M γs ^ ka * flatProjMomentNorm c h ≤
      Ca * GammaBox ν c σ H1 L1 M γs ^ (ka + kb + kc) * flatProjMomentNorm c h := by gcongr
  have l2 : Cb * GammaBox ν c σ H1 L1 M γs ^ kb * flatProjMomentNorm c h ≤
      Cb * GammaBox ν c σ H1 L1 M γs ^ (ka + kb + kc) * flatProjMomentNorm c h := by gcongr
  have l3 : Cc * GammaBox ν c σ H1 L1 M γs ^ kc * flatProjMomentNorm c h ≤
      Cc * GammaBox ν c σ H1 L1 M γs ^ (ka + kb + kc) * flatProjMomentNorm c h := by gcongr
  linarith

end UnforcedLeray.Short.PartIIa.N04_2_2_3
