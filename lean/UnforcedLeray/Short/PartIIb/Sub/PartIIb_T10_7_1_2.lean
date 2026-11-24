import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1

/-!
# `PartII-b:T10/7/1/2` (`GradWeakOfLift`): decomposition

Source of record: `the November 2 reference manuscript` lines 1912-1921, 1639-1668.

With `R = ε⁻¹`, `P = 2εc = 2c/R`, `ϱ = R s^{-1/2}`, `ρ`-derivative of the chart:
`∂_ρ s = -2ε s^{3/2}`, `∂_ρ q = s^{1/2}`, `∂_ρ η = -ε η s^{1/2}`, `∂_z η = s^{1/2}`, and
`dy dτ/P = π R² s^{-5/2} ds dη dq/c` (angular factor `2π` included).

* `ctLift c ε a φ` is the `c`-periodization in `q` of `s^a φ(s,q,η)` read at the chart point.
* `CTPair`: pairing of the lift (times the frame vector `e_i`) with `N_v u` is
  `(π R²/c) ∫ s^{a-2} u_i φ` (Jacobian, unfolding the `q`-periodization using periodicity of `u`).
* `CTDeriv`: the lift is a phase test and its `z`-derivative and radial derivative are lifts with
  `a + 1/2`: `∂_z lift(a,φ) = lift(a+1/2, ∂_η φ)`,
  `∂_ρ lift(a,φ) = lift(a+1/2, ∂_q φ - ε(2s∂_s + η∂_η)φ - 2aε φ)`.
* `GWZ`, `GWQ`: the two weak identities (test `HasPtwOp` with `Ψ e_i` for `j = 2`; with
  `(y_j/ϱ) Ψ e_i` summed over `j < 2`, where `Σ_j (y_j/ϱ)∂_j e_i = 0` and `div(y/ϱ) = 1/ϱ = ε s^{1/2}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The `c`-periodization in `q` of `s^a φ`, read at the chart point of `(τ, y)` (`R = ε⁻¹`). -/
def ctLift (c ε a : ℝ) (φ : Coord → ℝ) (x : ℝ × Space) : ℝ :=
  ∑' n : ℤ, (Axi.age ε⁻¹ x.2) ^ a *
    φ (Axi.age ε⁻¹ x.2, (Axi.phase ε⁻¹ x.1 x.2 + n * c, Axi.trans ε⁻¹ x.2))

/-- The meridional frame vector `e_0 = e_r`, `e_1 = e_z` (complexified). -/
def frameC (i : Fin 2) (y : Space) : CVec3 :=
  B0412.realC (Axi.frameL y (EuclideanSpace.single i 1))

/-- Smoothness/periodicity of the lift and its `z`- and `ρ`-derivatives. -/
def CTDeriv : Prop :=
  ∀ (c ε a : ℝ) (φ : Coord → ℝ), 0 < c → 0 < ε → IsCoordTest φ →
    IsPhaseTest (2 * ε * c) (ctLift c ε a φ) ∧
    (∀ x : ℝ × Space, x.2 ∉ Axi.axis →
      fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 2 1) =
        ctLift c ε (a + 1 / 2) (fun m => cpd 2 φ m) x) ∧
    (∀ x : ℝ × Space, x.2 ∉ Axi.axis →
      (x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) *
          fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 0 1) +
        (x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) *
          fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 1 1) =
        ctLift c ε (a + 1 / 2)
          (fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m) x)

/-- Pairing of the lift (times `e_i`) with `N_v u`. -/
def CTPair : Prop :=
  ∀ (c ε r a : ℝ) (φ : Coord → ℝ) (u : CProf) (i : Fin 2), 0 < c → 0 < ε → 1 < r → r < 3 →
    IsCoordTest φ → InHr c r u →
    pairF (2 * ε * c) (fun x => ((ctLift c ε a φ x : ℝ) : ℂ) • frameC i x.2) (NvC ε⁻¹ u) =
      (((Real.pi * ε⁻¹ ^ 2 / c : ℝ)) : ℂ) *
        ∫ x : Coord, (((x.1 ^ (a - 2) : ℝ)) : ℂ) * u x i * (φ x : ℂ)

/-- The `z`-derivative weak identity `∂_η b = Eb`. -/
def GWZ : Prop :=
  ∀ (c ε r : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3) (Qb Eb : CProf), 0 < c → 0 < ε →
    1 < r → r < 3 → InHr c r b → (∀ j, IsInYr (2 * ε * c) r (g j)) →
    (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
    QPeriodic c (sqrtS Eb) → AEStronglyMeasurable (sqrtS Eb) (hMeas c r) →
    (NvC ε⁻¹ (sqrtS Eb) =ᵐ[volume] g 2) → HasWeakVec vEta dZero b Eb

/-- The radial weak identity `Q_ε b = Qb`. -/
def GWQ : Prop :=
  ∀ (c ε r : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3) (Qb Eb : CProf), 0 < c → 0 < ε →
    1 < r → r < 3 → InHr c r b → (∀ j, IsInYr (2 * ε * c) r (g j)) →
    (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
    QPeriodic c (sqrtS Qb) → AEStronglyMeasurable (sqrtS Qb) (hMeas c r) →
    (NvC ε⁻¹ (sqrtS Qb) =ᵐ[volume] fun x : ℝ × Space =>
        (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x +
        (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x) →
    HasWeakVec (vQ ε) (dQ ε) b Qb

theorem gradWeakOfLift_of (hZ : GWZ) (hQ : GWQ) : GradWeakOfLift := by
  intro c ε r b g Qb Eb hc hε hr1 hr3 hb hgY hgp hQp hQm hEp hEm hE hQe
  exact ⟨hQ c ε r b g Qb Eb hc hε hr1 hr3 hb hgY hgp hQp hQm hQe,
    hZ c ε r b g Qb Eb hc hε hr1 hr3 hb hgY hgp hEp hEm hE⟩

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gradWeakOfLift_of
