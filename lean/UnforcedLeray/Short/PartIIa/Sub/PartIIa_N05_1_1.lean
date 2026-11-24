import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1

/-!
# `Sub/PartII-a_N05_1_1`: design of `PhaseD2CutoffSQE` (`PartII-a:N05/1/1`)

Source: `the November 2 reference manuscript`, lines 1789-1793
(`near:local-smoothing`: for a body source the graph controls `S b`, the gradient controls
`Q_ε b, ∂_η b`; with `∂_s = s⁻¹ S`, `∂_q = Q_ε + ε(2S + η∂_η + 1)` the cut-off output has a full
local `H¹` bound).

The leaf splits into three Props.
* `PhaseGradTransport` (G): the phase gradient `grad_v` of `v = U (liftVec w)` gives weak
  `Q_ε w`, `∂_η w` in `H` (weak identities on `cellMeasure c` against `IsMeridTest` fields).
* `PhaseGeneratorTransport` (T): `v ∈ D P ν 2` gives weak `S w` in `H` from `T0D v`
  (conjugation `N01.phaseSemigroupConj`: `T - 3/4 ↔ S - 1/4`).
* `PhaseCutoffProductRule` (P): cutting weak `(S, Q_ε, ∂_η)`-data off by `χ` gives `HasLocalSQE`
  with the stated `cellL2Norm` bound (pure analysis on `H`).
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1Org

/-- Weak `S`-derivative on `cellMeasure c` (periodised representatives): `∂_s w = s⁻¹ S w`
(source line 1791). -/
def WeakS (c : ℝ) (w Sw : HSpace c MeridC) : Prop :=
  ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (dsFromS (periodize c (Sw : Profile → MeridC)) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (periodize c (w : Profile → MeridC) p) (pdS φ p) ∂(cellMeasure c)

/-- Weak `∂_η`-derivative on `cellMeasure c` (source line 1791). -/
def WeakEta (c : ℝ) (w Ew : HSpace c MeridC) : Prop :=
  ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (periodize c (Ew : Profile → MeridC) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (periodize c (w : Profile → MeridC) p) (pdEta φ p) ∂(cellMeasure c)

/-- Weak `Q_ε = ∂_q - ε(K+1)` on `cellMeasure c` (source line 1650, 1792); the formal adjoint of
`Q_ε` against `ds dq dη` is `-(∂_q - ε(K+2))`, so the identity reads
`∫⟨Q w, φ⟩ = -∫⟨w, ∂_qφ - ε(Kφ + 2φ)⟩`. -/
def WeakQ (c ε : ℝ) (w Qw : HSpace c MeridC) : Prop :=
  ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (periodize c (Qw : Profile → MeridC) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (periodize c (w : Profile → MeridC) p)
        (pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p)) ∂(cellMeasure c)

/-- **(G) Gradient transport** (source lines 1789-1792: "the gradient controls `Q_ε b, ∂_η b`"):
the phase gradient of `v = U (liftVec w)` lifts `(Q_ε w, ∂_η w, ε w_r)`. -/
def PhaseGradTransport : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν c ε : ℝ), 0 < ν → ∀ (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
      ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
      ∀ (w : HSpace c MeridC) (v : D P ν 2) (grad_v : Fin 3 → Yq P 2),
        (v : Yq P 2) = U (B0223.liftVec hε hc hP w) →
        HasGrad (v : Yq P 2) grad_v →
        ∃ Qw Ew : HSpace c MeridC, WeakQ c ε w Qw ∧ WeakEta c w Ew ∧
          ‖Qw‖ + ‖Ew‖ ≤ C * (‖(v : Yq P 2)‖ + ∑ j : Fin 3, ‖grad_v j‖)

/-- **(T) Generator transport** (source lines 1789-1791: "the graph controls `S b`"):
`T - 3/4` conjugates to `S - 1/4` (`N01.phaseSemigroupConj`), so `T0D v` gives a weak `S w`. -/
def PhaseGeneratorTransport : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν c ε : ℝ), 0 < ν → ∀ (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
      ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
      ∀ (w : HSpace c MeridC) (v : D P ν 2),
        (v : Yq P 2) = U (B0223.liftVec hε hc hP w) →
        ∃ Sw : HSpace c MeridC, WeakS c w Sw ∧ ‖Sw‖ ≤ C * (‖(v : Yq P 2)‖ + ‖T0D v‖)

/-- **(P) Cutoff product rule** (source lines 1791-1792): cutting weak `(S, Q_ε, ∂_η)` data of
`w ∈ H` off by `χ` (`IsNearCutoff`) gives `HasLocalSQE` for `mulChi χ w` with
`u = flatStressCutRep c χ w`, `Su = χ S w + s ∂_sχ w`, `Eu = χ ∂_η w + ∂_ηχ w`,
`Qu = χ Q w + ∂_qχ w - ε(2 s ∂_sχ + η ∂_ηχ) w`. -/
def PhaseCutoffProductRule : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs → 0 ≤ M →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (w Sw Qw Ew : HSpace c MeridC),
        WeakS c w Sw → WeakQ c ε w Qw → WeakEta c w Ew →
        ∃ u Su Qu Eu : Profile → MeridC,
          HasLocalSQE c σ H1 L1 ε (mulChi (measureH c) χ hm hB w) u Su Qu Eu ∧
          cellL2Norm c u + cellL2Norm c Su + cellL2Norm c Qu + cellL2Norm c Eu ≤
            C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * (‖w‖ + ‖Sw‖ + ‖Qw‖ + ‖Ew‖)

/-- Assembly: `PhaseD2CutoffSQE` from (G), (T), (P). Composed in task `PartII-a:N05/1/1`. -/
theorem phaseD2CutoffSQE_of (hG : PhaseGradTransport) (hT : PhaseGeneratorTransport)
    (hP' : PhaseCutoffProductRule) : PhaseD2CutoffSQE := by
  obtain ⟨C_G, hC_G, hG⟩ := hG
  obtain ⟨C_T, hC_T, hT⟩ := hT
  obtain ⟨k, C_P, hC_P, hPR⟩ := hP'
  refine ⟨k, C_P * (1 + C_T + C_G), by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ hχ1 hm B hB ε hε hε1 P _ hP hP1 U hU w v
    grad_v hv hgrad
  obtain ⟨Qw, Ew, hQ, hE, hQE⟩ := hG ν c ε hν hc hε hε1 P hP hP1 U hU w v grad_v hv hgrad
  obtain ⟨Sw, hS, hSb⟩ := hT ν c ε hν hc hε hε1 P hP hP1 U hU w v hv
  obtain ⟨u, Su, Qu, Eu, hsqe, hbd⟩ :=
    hPR ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ hχ1 hm B hB ε hε hε1 w Sw Qw Ew hS hQ hE
  refine ⟨u, Su, Qu, Eu, hsqe, hbd.trans ?_⟩
  have hnorm : ‖w‖ = ‖(v : Yq P 2)‖ := by
    rw [hv, U.norm_map, (B0223.liftVec hε hc hP).norm_map]
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG0 : 0 ≤ G ^ k := by
    have : 1 ≤ G := N05_1Aux.one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
    positivity
  have n1 := norm_nonneg (v : Yq P 2)
  have n2 := norm_nonneg (T0D v)
  have n3 : 0 ≤ ∑ j : Fin 3, ‖grad_v j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have key : ‖w‖ + ‖Sw‖ + ‖Qw‖ + ‖Ew‖ ≤
      (1 + C_T + C_G) * (‖(v : Yq P 2)‖ + ‖T0D v‖ + ∑ j : Fin 3, ‖grad_v j‖) := by
    rw [hnorm]
    nlinarith [mul_nonneg hC_T n1, mul_nonneg hC_T n2, mul_nonneg hC_G n1, mul_nonneg hC_G n3,
      mul_nonneg hC_T n3, mul_nonneg hC_G n2]
  calc C_P * G ^ k * (‖w‖ + ‖Sw‖ + ‖Qw‖ + ‖Ew‖)
      ≤ C_P * G ^ k * ((1 + C_T + C_G) *
          (‖(v : Yq P 2)‖ + ‖T0D v‖ + ∑ j : Fin 3, ‖grad_v j‖)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hC_P hG0)
    _ = C_P * (1 + C_T + C_G) * G ^ k *
          (‖(v : Yq P 2)‖ + ‖T0D v‖ + ∑ j : Fin 3, ‖grad_v j‖) := by ring

end N05_1_1Org

end UnforcedLeray.Short.PartIIa
