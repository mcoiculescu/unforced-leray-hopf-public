import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4

/-!
# Part II-b, task `PartII-b:T13/1/4/1` (`chmEuclid`): decomposition

Source: `the November 2 reference manuscript` (SP) lines 1933-1935 and 1377-1424
(`UnforcedLeray.Parabolic.heat_maximal_regularity`, `Lib/ParabolicB.lean:158`, `d = 2`).

`ChmEuclid` (complex, on `Coord = ℝ × (ℝ × ℝ)`) follows from the real-valued estimate
(`ChmEuclidReal`, the transport along the isometry `Coord ≃ PS 2`) and the complex splitting
(`ChmEuclidSplit`, real and imaginary parts, constant `2 C`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- `(∂_s - νΔ_{q,η}) u = f` in distributions on `ℝ × ℝ²`, real valued. -/
def IsCylHeatR (ν : ℝ) (u f : Coord → ℝ) : Prop :=
  ∀ φ, IsSTTestCoord φ → ∫ x, u x * cylHeatT ν φ x = ∫ x, f x * φ x

/-- The real Euclidean estimate on `Coord` for fixed `r` and constant `C` (SP 1377-1424). -/
def ChmEuclidRealAt (r C : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u F : Coord → ℝ,
    AEStronglyMeasurable u volume → AEStronglyMeasurable F volume →
    eLpNorm u (ENNReal.ofReal r) volume < ⊤ → eLpNorm F (ENNReal.ofReal r) volume < ⊤ →
    IsCylHeatR ν u F →
    ∃ (Dt : Coord → ℝ) (D2 : Fin 2 → Fin 2 → Coord → ℝ),
      AEStronglyMeasurable Dt volume ∧ (∀ i j, AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoord φ → ∫ x, u x * cpd 0 φ x = -∫ x, Dt x * φ x) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * cpd i.succ (fun y => cpd j.succ φ y) x = ∫ x, D2 i j x * φ x) ∧
      eLpNorm Dt (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume ∧
      ∀ i j, eLpNorm (fun x => ν * D2 i j x) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume

/-- The complex Euclidean estimate on `Coord` for fixed `r` and constant `C`. -/
def ChmEuclidAt (r C : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u F : Coord → ℂ,
    AEStronglyMeasurable u volume → AEStronglyMeasurable F volume →
    eLpNorm u (ENNReal.ofReal r) volume < ⊤ → eLpNorm F (ENNReal.ofReal r) volume < ⊤ →
    IsCylHeat ν u F →
    ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      AEStronglyMeasurable Dt volume ∧ (∀ i j, AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoord φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, Dt x * (φ x : ℂ)) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) ∧
      eLpNorm Dt (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume ∧
      ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume

/-- **Sub-lemma 1 (real Euclidean estimate on `Coord`, SP 1377-1424).** Transport of
`Parabolic.heat_maximal_regularity` (`d = 2`) along the measure-preserving linear isometry
`ℝ × (ℝ × ℝ) ≃ ℝ × EuclideanSpace ℝ (Fin 2)`; tests, weak derivatives and `L^r` norms are
transported back and forth. -/
def ChmEuclidReal : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ChmEuclidRealAt r C

/-- **Sub-lemma 2 (complex splitting).** If the real estimate holds with constant `C`, the complex
one holds with constant `2 C`: `Re u, Im u` solve the real equations with sources `Re F, Im F`
(`ν` and the tests are real), take `Dt = Dt_re + i Dt_im`, `D2 = D2_re + i D2_im`, and use
`‖Re F‖_r, ‖Im F‖_r ≤ ‖F‖_r`, `‖g‖_r ≤ ‖Re g‖_r + ‖Im g‖_r`. -/
def ChmEuclidSplit : Prop :=
  ∀ r C : ℝ, 1 < r → 0 < C → ChmEuclidRealAt r C → ChmEuclidAt r (2 * C)

theorem chmEuclid_of (h1 : ChmEuclidReal) (h2 : ChmEuclidSplit) : ChmEuclid := by
  intro r hr
  obtain ⟨C, hC, hR⟩ := h1 r hr
  exact ⟨2 * C, by positivity, h2 r C hr hC hR⟩

end UnforcedLeray.Short.IIb
