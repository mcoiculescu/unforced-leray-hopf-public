import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5

/-!
# Decomposition of `CgiLimit` (task `PartII-b:T13/1/5/6`)

Source `the November 2 reference manuscript`
1932-1935 (passage to the limit).  Three steps:

* `CgiLimitCauchy`: applying `AprioriAt` to the differences `w n - w m` shows `∂_i w n` is Cauchy
  in `L^r(cylMeas c)`; completeness gives a periodic measurable limit `D1 i`.
* `CgiLimitWeak`: the weak identity `∫ u ∂_i φ = -∫ D1 i φ`, by integration by parts for the smooth
  `w n` and passage to the limit (Hölder on a finite union of period cells).
* `CgiLimitNorm`: the inequality, by passing `AprioriAt` for `w n` to the limit.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- **Step 1 (Cauchy + completeness, SP 1932-1933).** -/
def CgiLimitCauchy : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c C : ℝ, 0 < c → 0 < C → AprioriAt c r C →
    ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) (w : ℕ → Coord → ℂ),
    CgiApprox c r u D2 w → AEStronglyMeasurable u volume →
    (∀ k l : Fin 2, AEStronglyMeasurable (D2 k l) volume) →
    ∃ D1 : Fin 2 → Coord → ℂ,
      (∀ i, QPeriodicS c (D1 i) ∧ AEStronglyMeasurable (D1 i) volume) ∧
      ∀ i : Fin 2, Tendsto (fun n => cylNorm c r (fun x => cdv i.succ (w n) x - D1 i x))
        atTop (𝓝 0)

/-- **Step 2 (weak identity, SP 1933-1934).** -/
def CgiLimitWeak : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c →
    ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) (w : ℕ → Coord → ℂ),
    CgiApprox c r u D2 w → QPeriodicS c u → AEStronglyMeasurable u volume →
    ∀ D1 : Fin 2 → Coord → ℂ,
      (∀ i, QPeriodicS c (D1 i) ∧ AEStronglyMeasurable (D1 i) volume) →
      (∀ i : Fin 2, Tendsto (fun n => cylNorm c r (fun x => cdv i.succ (w n) x - D1 i x))
        atTop (𝓝 0)) →
      ∀ (i : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ φ x : ℂ) = -∫ x, D1 i x * (φ x : ℂ)

/-- **Step 3 (inequality in the limit, SP 1934-1935).** -/
def CgiLimitNorm : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c C : ℝ, 0 < c → 0 < C → AprioriAt c r C →
    ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) (w : ℕ → Coord → ℂ),
    CgiApprox c r u D2 w → QPeriodicS c u → AEStronglyMeasurable u volume →
    (∀ k l : Fin 2, AEStronglyMeasurable (D2 k l) volume) →
    ∀ D1 : Fin 2 → Coord → ℂ,
      (∀ i, QPeriodicS c (D1 i) ∧ AEStronglyMeasurable (D1 i) volume) →
      (∀ i : Fin 2, Tendsto (fun n => cylNorm c r (fun x => cdv i.succ (w n) x - D1 i x))
        atTop (𝓝 0)) →
      ∀ (i : Fin 2) (lam : ℝ), 0 < lam → cylNorm c r (D1 i) ≤ cgiRhs c r C lam u D2

theorem cgiLimit_of (h1 : CgiLimitCauchy) (h2 : CgiLimitWeak) (h3 : CgiLimitNorm) :
    CgiLimit := by
  intro r hr c C hc hC hA u D2 w hw hup hum hD2
  obtain ⟨D1, hD1, hT⟩ := h1 r hr c C hc hC hA u D2 w hw hum hD2
  exact ⟨D1, hD1, fun i φ hφ => h2 r hr c hc u D2 w hw hup hum D1 hD1 hT i φ hφ,
    fun i lam hl => h3 r hr c C hc hC hA u D2 w hw hup hum hD2 D1 hD1 hT i lam hl⟩

end UnforcedLeray.Short.IIb
