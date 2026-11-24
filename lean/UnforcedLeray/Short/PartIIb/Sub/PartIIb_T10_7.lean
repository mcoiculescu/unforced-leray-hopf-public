import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# `PartII-b:T10/7` (`GradRecovery`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1912-1921
(`∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`) and 1639-1668 (chart, `Q_ε`).

Two leaves: existence of the profile-side weak derivatives with the measurability/periodicity needed
to apply `phaseLpNorm_NvC` (`GradWeak`), and the pointwise chart bound `|N_v(√s Q_ε b)| + |N_v(√s ∂_η b)|
≲ |∇ N_v b|` integrated over a period (`GradBound`).  The target follows (`gradRecovery_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- **`T10/7/1`** (SP 1912-1921; converse of the gradient chart identities): if the spatial gradient of
the lift of `b ∈ H_r` lies in `Y_r`, the profile-side weak derivatives `Q_ε b`, `∂_η b` exist, and
`√s Q_ε b`, `√s ∂_η b` are `c`-periodic and `H_r`-measurable.  Proof: test against `c`-periodized lifts
of coordinate tests (the chart change of variables, as in `ChartDrift` of T10/6); the weak derivatives
are the `ρ`- and `z`-components of `g_j` read through the inverse chart (`Axi.chart`,
`Lib/AxisymmetricB/RingChart`; `invLift`), so measurability and periodicity come from those of `g_j`. -/
def GradWeak : Prop :=
  ∀ (c ε r : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → r < 3 →
    InHr c r b → (∀ j, IsInYr (2 * ε * c) r (g j)) →
    (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
    ∃ Qb Eb : CProf, HasWeakVec (vQ ε) (dQ ε) b Qb ∧ HasWeakVec vEta dZero b Eb ∧
      QPeriodic c (sqrtS Qb) ∧ AEStronglyMeasurable (sqrtS Qb) (hMeas c r) ∧
      QPeriodic c (sqrtS Eb) ∧ AEStronglyMeasurable (sqrtS Eb) (hMeas c r)

/-- **`T10/7/2`** (SP 1912-1921, 1639-1668): given the weak derivatives, the lifts of `√s Q_ε b` and
`√s ∂_η b` are pointwise bounded by the gradient: `|N_v(√s Q_ε b)| = s|Q_ε b| ≤ |∂_ρ N_v b|` and
`|N_v(√s ∂_η b)| = s|∂_η b| ≤ |∂_z N_v b|` (a.e. in `(τ, y)` through the chart, identification of `g_j`
with the Cartesian derivative of the lift by uniqueness of distributional derivatives), hence
Minkowski over `j` and monotonicity of `phaseLpNorm`. -/
def GradBound : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∃ K : ℝ, 0 < K ∧
    ∀ (c ε : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3) (Qb Eb : CProf), 0 < c → 0 < ε →
      InHr c r b → (∀ j, IsInYr (2 * ε * c) r (g j)) →
      (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
      HasWeakVec (vQ ε) (dQ ε) b Qb → HasWeakVec vEta dZero b Eb →
      QPeriodic c (sqrtS Qb) → AEStronglyMeasurable (sqrtS Qb) (hMeas c r) →
      QPeriodic c (sqrtS Eb) → AEStronglyMeasurable (sqrtS Eb) (hMeas c r) →
      phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ (sqrtS Qb)) + phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ (sqrtS Eb)) ≤
        ENNReal.ofReal K * ∑ j, phaseLpNorm (2 * ε * c) r (g j)

theorem gradRecovery_of (h1 : GradWeak) (h2 : GradBound) : GradRecovery := by
  intro r hr1 hr3
  obtain ⟨K, hK, hKb⟩ := h2 r hr1 hr3
  refine ⟨K, hK, ?_⟩
  intro c ε b g hc hε hb hgY hgp
  obtain ⟨Qb, Eb, hQ, hE, hQp, hQm, hEp, hEm⟩ := h1 c ε r b g hc hε hr1 hr3 hb hgY hgp
  refine ⟨Qb, Eb, hQ, hE, ?_⟩
  have hr0 : 0 < r := by linarith
  have e1 := phaseLpNorm_NvC hc hr0 hε (sqrtS Qb) hQp hQm
  have e2 := phaseLpNorm_NvC hc hr0 hε (sqrtS Eb) hEp hEm
  have := hKb c ε b g Qb Eb hc hε hb hgY hgp hQ hE hQp hQm hEp hEm
  rw [e1, e2, ← mul_add] at this
  exact this

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gradRecovery_of
