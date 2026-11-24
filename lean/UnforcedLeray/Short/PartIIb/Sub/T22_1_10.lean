import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

/-!
# `PartII-b:T22/1/10` (`ConvRegular`) split along its conjuncts

Source: `the November 2 reference manuscript` lines 2074-2093 and 2103-2105; the
statements are standard heat-kernel calculus (see the docstring of `ConvRegular` in
`Sub/T22_1/Stages.lean`). The four leaves are

* `CRDeriv` : `G(τ) ∈ C²` and the two derivative formulas,
* `CRSize`  : the weighted `W2` bound (given the derivative formulas),
* `CRCont`  : joint continuity of `G`, `∇G`, `∇²G`,
* `CRPer`   : periodicity,

and `convRegular_of` reassembles `ConvRegular` with `K = 2 e^{ν(T-s)} (7 + 6 ν^{-1/2})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

/-- The hypotheses on `(F, b)` of `ConvRegular`. -/
def CRHyp (s T : ℝ) (F : ℝ → Pl → ℝ) (b : ℝ → ℝ) : Prop :=
  FReg s T F ∧ ContinuousOn b (Icc s T) ∧ (∀ r ∈ Icc s T, 0 ≤ b r) ∧
    ∀ r ∈ Icc s T, WB (b r) (F r) ∧ ∀ j : Fin 2, WB (b r) (B0579.pd j (F r))

/-- The derivative formulas for `G(τ) = duhamelConv ν s F τ`. -/
def CRFormulas (ν s : ℝ) (F : ℝ → Pl → ℝ) (τ : ℝ) : Prop :=
  (∀ (i : Fin 2) (x : Pl), B0579.pd i (duhamelConv ν s F τ) x =
    ∫ r in s..τ, heatSGd i (ν * (τ - r)) (F r) x) ∧
  (∀ (i j : Fin 2) (x : Pl), B0579.pd i (B0579.pd j (duhamelConv ν s F τ)) x =
    ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd j (F r)) x)

/-- The constant of `ConvRegular`. -/
def crK (ν s T : ℝ) : ℝ := 2 * Real.exp (ν * (T - s)) * (7 + 6 * ν ^ (-(1 / 2 : ℝ)))

/-- **Leaf `T22/1/10/1`.** `G(τ)` is `C²` with the derivative formulas: differentiate under the
`r`-integral (`hasFDerivAt_integral_of_dominated_of_fderiv_le`) using `HeatGradFormula`,
`HeatCommute`, `HeatWBounds` and the integrable majorant `2 e^{ν L}(1 + a^{-1/2}) b(r)`,
`a = ν(τ - r)`; second derivative by applying the first step to `∂_j F(r)`. -/
def CRDeriv : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  CRHyp s T F b → ∀ τ ∈ Icc s T, ContDiff ℝ 2 (duhamelConv ν s F τ) ∧ CRFormulas ν s F τ

/-- **Leaf `T22/1/10/2`.** The weighted bound `W2(G(τ)) cosh η ≤ K ∫_s^τ (1 + (τ-r)^{-1/2}) b(r) dr`
given the derivative formulas: `HeatWBounds` with `a = ν(τ - r)` for the `1 + 2 + 4` terms of `W2`,
`a^{-1/2} = ν^{-1/2} (τ-r)^{-1/2}`, integrability by
`Lib/BudgetsGronwall/SingularVolterra.lean` (`intervalIntegrable_kernel_mul`). -/
def CRSize : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  CRHyp s T F b → ∀ τ ∈ Icc s T, CRFormulas ν s F τ → ∀ x : Pl,
    W2 (duhamelConv ν s F τ) x * Real.cosh x.2 ≤
      crK ν s T * ∫ r in s..τ, (1 + (τ - r) ^ (-(1 / 2 : ℝ))) * b r

/-- **Leaf `T22/1/10/3`.** Joint continuity on `[s, T] × Pl` of `G`, `∂_j G`, `∂_i ∂_j G`
(dominated convergence after `r = τ - t`, `HeatCont`, singular majorant). -/
def CRCont : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  CRHyp s T F b →
    ContinuousOn (fun z : ℝ × Pl => duhamelConv ν s F z.1 z.2) (Icc s T ×ˢ univ) ∧
    (∀ j : Fin 2, ContinuousOn (fun z : ℝ × Pl => B0579.pd j (duhamelConv ν s F z.1) z.2)
      (Icc s T ×ˢ univ)) ∧
    (∀ i j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (duhamelConv ν s F z.1)) z.2)
        (Icc s T ×ˢ univ))

/-- **Leaf `T22/1/10/4`.** Periodicity of `G(τ)` from `HeatPeriodic` and linearity of the integral. -/
def CRPer : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  CRHyp s T F b → ∀ c : ℝ, (∀ r ∈ Icc s T, ∀ y : Pl, F r (y.1 + c, y.2) = F r y) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, duhamelConv ν s F τ (x.1 + c, x.2) = duhamelConv ν s F τ x

theorem convRegular_of (hD : CRDeriv) (hS : CRSize) (hC : CRCont) (hP : CRPer) : ConvRegular := by
  intro ν s T hν hsT
  refine ⟨crK ν s T, ?_, ?_⟩
  · unfold crK
    positivity
  · intro F hF b hb hb0 hFb
    have hH : CRHyp s T F b := ⟨hF, hb, hb0, hFb⟩
    obtain ⟨hc0, hc1, hc2⟩ := hC ν s T hν hsT F b hH
    refine ⟨fun τ hτ => ⟨(hD ν s T hν hsT F b hH τ hτ).1, (hD ν s T hν hsT F b hH τ hτ).2.1,
      (hD ν s T hν hsT F b hH τ hτ).2.2⟩, hc0, hc1, hc2, ?_, ?_⟩
    · exact fun c hcp τ hτ x => hP ν s T hν hsT F b hH c hcp τ hτ x
    · intro τ hτ x
      exact hS ν s T hν hsT F b hH τ hτ (hD ν s T hν hsT F b hH τ hτ).2 x

end UnforcedLeray.Short.IIb.CylPDE
