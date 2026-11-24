import UnforcedLeray.Short.PartIIb.Bridge.Dict
import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F07Surjective
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain
import UnforcedLeray.Short.PartIIa.Sub.F08
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F14_1_3
import UnforcedLeray.Units.B0005.Bridge.Commute

/-!
# Bridge: the Part II-a abstract model and the pointwise-field model of Parts II-b / III-b

Source of record: `the November 2 reference manuscript`, lines 1339-1364 (the free
Cartesian equation, Lemma `bg:common-body-graph`), 1409-1440 (uniqueness, maximal domain, the
adjoint), 1478-1500 (Fubini packaging, Leray commutes).

The dictionary (`Bridge/Rep.lean`, `Bridge/Dict.lean`): `toYq`, `HasRepY`, `hasPtwOp_iff_hasPhaseOp`.
Here:

* `isFreeResponse_iff` (**(c)**) : for `f ∈ Y_r`, `w` a field representing `W : Y_r`,
  `IsFreeResponse ν μ r P f w ↔ ∃ hW : W ∈ D_r, W ∈ Y_σ ∧ bodyOp μ ⟨W, hW⟩ = 𝐏 (toYq f)`;
* `field_response_exists` (**(d)**) and `field_graph_bound` (**(d)**), from the proved Part II-a
  facts (`commonBodyProjected_of lerayYResolventComm`, `commonBodyGraphBound`).

Two source facts about the Leray projection and solenoidal tests, which the field model needs
because `IsFreeResponse` tests the equation only against *solenoidal* tests, are isolated as Props
(`LerayPairSol`, `SolSeparation`, source 1358-1361, 1498-1500) and carried as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-- **Leray projection is invisible on solenoidal tests** (source 1358-1361: "Its projected
inverse is obtained by applying Cartesian Leray projection to `f`", `⟪Φ, 𝐏f⟫ = ⟪𝐏Φ, f⟫ = ⟪Φ, f⟫` for
`div Φ = 0`, `Φ` a smooth compactly supported (in `y`) periodic test). -/
def LerayPairSol : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (h1 : 1 < q) (hq : q ≠ ⊤) (P : ℝ) [Fact (0 < P)] (F : Yq P q)
    (Φ : ℝ × Space → CVec3), IsSolTest P Φ →
      phasePair P q Φ (lerayY P q h1 hq F) = phasePair P q Φ F

/-- **Solenoidal tests separate `Y_{q,σ}`** (source 1409-1412, 1498-1500: a solenoidal `s ∈ Y_q`,
`1 < q < ∞`, orthogonal to all solenoidal phase tests is a harmonic gradient in `L^q(ℝ³)` for
a.e. phase, hence zero). -/
def SolSeparation : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (s : Yq P q),
    IsPhaseSolenoidal s → (∀ Φ : ℝ × Space → CVec3, IsSolTest P Φ → phasePair P q Φ s = 0) → s = 0

section Dict

variable {P ν : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `bodyOp μ w` paired with a phase test is the pairing of `(μ + L₀ᵗ)Φ` with `w`. -/
theorem phasePair_bodyOp (μ : ℂ) (w : D P ν q) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q Φ (bodyOp P ν q μ w) =
      phasePair P q (fun x => L0T ν Φ x + μ • Φ x) (w : Yq P q) := by
  have h1 : IsPhaseTest P (L0T ν Φ) := isPhaseTest_L0T hΦ ν
  have h2 : IsPhaseTest P (μ • Φ) := hΦ.const_smul μ
  have h3 : (fun x => L0T ν Φ x + μ • Φ x) = L0T ν Φ + μ • Φ := rfl
  have hL := hasPhaseOp_L0D w Φ hΦ
  simp only [bodyOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_subtype,
    L0L_apply]
  rw [h3, phasePair_add h1 h2, phasePair_const_smul hΦ, map_add, map_smul, ← hL, smul_eq_mul]
  ring

/-- The body operator maps `D_σ` into `Y_σ` (`div` commutes with `L₀`, via
`IsPhaseSolenoidal.of_hasHLap`, `.of_hasT0`). -/
theorem bodyOp_mem_Ysigma (μ : ℂ) (w : D P ν q) (hw : (w : Yq P q) ∈ Ysigma P q) :
    bodyOp P ν q μ w ∈ Ysigma P q := by
  have hn : nuLapD w ∈ Ysigma P q :=
    mem_Ysigma.2 (UnforcedLeray.B0005.IsPhaseSolenoidal.of_hasHLap (mem_Ysigma.1 hw)
      (hasPhaseOp_nuLapD w))
  have ht : T0D w ∈ Ysigma P q :=
    mem_Ysigma.2 (UnforcedLeray.B0005.IsPhaseSolenoidal.of_hasT0 (mem_Ysigma.1 hw)
      (hasPhaseOp_T0D w))
  simp only [bodyOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_subtype,
    L0L_apply, L0D]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hw)
    (Submodule.sub_mem _ (Submodule.sub_mem _ ht hn) (Submodule.smul_mem _ _ hw))

/-- **(c), abstract side**: for `w ∈ D_σ`, the equation tested on solenoidal tests is
`bodyOp μ w = 𝐏F`. -/
theorem bodyOp_eq_leray_iff (hLP : LerayPairSol) (hSS : SolSeparation) (h1 : 1 < q) (hq : q ≠ ⊤)
    (μ : ℂ) (w : D P ν q) (hw : (w : Yq P q) ∈ Ysigma P q) (F : Yq P q) :
    (∀ Φ, IsSolTest P Φ → phasePair P q Φ (bodyOp P ν q μ w) = phasePair P q Φ F) ↔
      bodyOp P ν q μ w = lerayY P q h1 hq F := by
  constructor
  · intro h
    have hs : bodyOp P ν q μ w - lerayY P q h1 hq F ∈ Ysigma P q :=
      Submodule.sub_mem _ (bodyOp_mem_Ysigma μ w hw)
        (mem_Ysigma.2 (lerayY_isPhaseSolenoidal h1 hq F))
    have := hSS q h1 hq P _ (mem_Ysigma.1 hs) (fun Φ hΦ => by
      rw [map_sub, h Φ hΦ, hLP q h1 hq P F Φ hΦ, sub_self])
    exact sub_eq_zero.1 this
  · intro h Φ hΦ
    rw [h, hLP q h1 hq P F Φ hΦ]

end Dict

end UnforcedLeray.Short.IIb
