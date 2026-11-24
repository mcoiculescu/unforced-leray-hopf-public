import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7

/-!
# `PartII-b:T10/7/1` (`GradWeak`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1912-1921
(`∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`) and 1639-1668 (chart, `Q_ε`).

`g_j = ∂_{y_j} (N_v b)` (`HasPtwOp` with `Lt Φ = -∂_jΦ`).  Two leaves:

* `GradLiftRead` : the profile-side functions `Qb, Eb` exist, are `c`-periodic and `H_r`-measurable
  after the factor `√s`, and their lifts are the `z`-derivative `g_2` and the radial derivative
  `Σ_{j<2} (y_j/ϱ) g_j` of the lift (a.e.).  Existence is by reading `g` through the inverse chart;
  that the radial/`z` derivatives are functions of `(s, ξ, η)` only comes from the rotation and
  dilation invariance of `N_v b` and uniqueness of weak derivatives (SP 1912-1921).
* `GradWeakOfLift` : given such `Qb, Eb`, the chart pairing transfer (test `HasPtwOp` against
  `c`-periodized lifts of coordinate tests, combined with weights `y_j/ϱ`, change of variables
  `Axi.chart`) gives the weak identities `Q_ε b = Qb`, `∂_η b = Eb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- **Leaf `T10/7/1/1`** (SP 1912-1921, 1639-1668): existence, periodicity, measurability and the
a.e. lift identities `N_v(√s E b) = ∂_z N_v b`, `N_v(√s Q b) = ∂_ρ N_v b`. -/
def GradLiftRead : Prop :=
  ∀ (c ε r : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → r < 3 →
    InHr c r b → (∀ j, IsInYr (2 * ε * c) r (g j)) →
    (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
    ∃ Qb Eb : CProf,
      QPeriodic c (sqrtS Qb) ∧ AEStronglyMeasurable (sqrtS Qb) (hMeas c r) ∧
      QPeriodic c (sqrtS Eb) ∧ AEStronglyMeasurable (sqrtS Eb) (hMeas c r) ∧
      (NvC ε⁻¹ (sqrtS Eb) =ᵐ[volume] g 2) ∧
      (NvC ε⁻¹ (sqrtS Qb) =ᵐ[volume] fun x : ℝ × Space =>
        (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x +
        (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x)

/-- **Leaf `T10/7/1/2`** (SP 1912-1921): chart pairing transfer.  Given `Qb, Eb` whose lifts are
the radial and `z` derivatives of `N_v b`, the weak identities `Q_ε b = Qb`, `∂_η b = Eb` hold:
test `HasPtwOp` against `c`-periodized lifts `Φ_φ` of coordinate tests (with weights `y_j/ϱ` for the
radial one), change variables by `Axi.chart`; integrability by Hölder and `phaseLpNorm_NvC`. -/
def GradWeakOfLift : Prop :=
  ∀ (c ε r : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3) (Qb Eb : CProf), 0 < c → 0 < ε →
    1 < r → r < 3 → InHr c r b → (∀ j, IsInYr (2 * ε * c) r (g j)) →
    (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
    QPeriodic c (sqrtS Qb) → AEStronglyMeasurable (sqrtS Qb) (hMeas c r) →
    QPeriodic c (sqrtS Eb) → AEStronglyMeasurable (sqrtS Eb) (hMeas c r) →
    (NvC ε⁻¹ (sqrtS Eb) =ᵐ[volume] g 2) →
    (NvC ε⁻¹ (sqrtS Qb) =ᵐ[volume] fun x : ℝ × Space =>
        (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x +
        (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x) →
    HasWeakVec (vQ ε) (dQ ε) b Qb ∧ HasWeakVec vEta dZero b Eb

theorem gradWeak_of (h1 : GradLiftRead) (h2 : GradWeakOfLift) : GradWeak := by
  intro c ε r b g hc hε hr1 hr3 hb hgY hgp
  obtain ⟨Qb, Eb, hQp, hQm, hEp, hEm, hE, hQ⟩ := h1 c ε r b g hc hε hr1 hr3 hb hgY hgp
  obtain ⟨w1, w2⟩ := h2 c ε r b g Qb Eb hc hε hr1 hr3 hb hgY hgp hQp hQm hEp hEm hE hQ
  exact ⟨Qb, Eb, w1, w2, hQp, hQm, hEp, hEm⟩

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gradWeak_of
