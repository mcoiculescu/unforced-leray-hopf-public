import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1

/-!
# `Sub/PartII-a_N05_1_1/G/Defs`: Corrected `s^{1/2}`-weighted gradient transport (`PartII-a:N05/1/1/1`)

Source: `the November 2 reference manuscript`,
lines 1644–1648, 1679–1683 (`near:free-energy`), and 1789–1793 (`near:local-smoothing`).

## R5 / R11 Note on `N05_1_1Org.PhaseGradTransport`

In the manuscript (lines 1644–1646, 1680), the velocity space is `H = L²(s^{-3/2} ds dq dη)` while
the gradient/tensor space is `H_T = L²(s^{-1/2} ds dq dη)`:
`‖b‖_H + √ν ‖(Q_ε b, ∂_η b, ε b_r)‖_{H_T} ≤ C ν^{-1/2} ‖M‖_{H_T}`.
Equivalently, under the isometric phase lift `U ∘ B0223.liftVec : H → Y_2`, the Cartesian phase
gradient `∇_y v` (`y = x/ε`, `s = (ε r_y)⁻²`) lifts `(s^{1/2} Q_ε w, s^{1/2} ∂_η w, s^{1/2} ε w_r)`
in `H` (since `∂_{y_2} η = (ε r_y)⁻¹ = s^{1/2}` and `∂_{r_y}(r_y⁻¹ w) = r_y⁻¹ s^{1/2} Q_ε w`).

Consequently, `N05_1_1Org.PhaseGradTransport` (which omits `s^{1/2}` and asks for unweighted
`Q_ε w, ∂_η w ∈ H` bounded by `C * (‖v‖_{Y_2} + ∑_j ‖grad_v j‖_{Y_2})`) is **mathematically false**
as `s → 0⁺` (`r_y → +∞`): smooth time-independent axisymmetric fields
`v_R(τ, y) = R^{-1/2} χ₁(r_y - R) χ₂(y_2) e_z ∈ D P ν 2` have `‖v_R‖_{Y_2} + ∑_j ‖grad_v_R j‖_{Y_2} = O(1)`
while `‖∂_η w_R‖_H = ‖s^{-1/2} (s^{1/2} ∂_η w_R)‖_H ≳ ε R → +∞`.

Per R11 (`Sub/PartII-a_N05_1_1.lean` is imported by accepted `PartII-a:N05/1/3`), we place the
corrected `s^{1/2}`-weighted weak identities (`WeakQWt`, `WeakEtaWt`), the true gradient transport
`PhaseGradTransportWt`, the weighted cutoff product rule `PhaseCutoffProductRuleWt`, and the
assembly `phaseD2CutoffSQE_of_wt : PhaseGradTransportWt → PhaseGeneratorTransport →
PhaseCutoffProductRuleWt → PhaseD2CutoffSQE` here. On `supp χ ⊆ {σ ≤ s ≤ H₁}` (`σ > 0`), the factor
`s^{-1/2} ≤ σ^{-1/2} ≤ 1 + σ⁻¹ ≤ Γ` is absorbed into `Γ^k`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1G

/-- Conversion from an `s^{1/2}`-weighted `H`-profile (`H_T` regularity) to the unweighted derivative:
`f_unwt(p) = s^{-1/2} f(p)` (analogous to `dsFromS` for `∂_s = s⁻¹ S`). -/
noncomputable def fromWt (f : Profile → MeridC) (p : Profile) : MeridC :=
  (p.1 ^ (-(1 / 2 : ℝ))) • f p

/-- Weak `∂_η`-derivative on `cellMeasure c` with `Ew = s^{1/2} ∂_η w ∈ H`
(source lines 1646, 1680, 1790): `∂_η w = s^{-1/2} Ew`. -/
def WeakEtaWt (c : ℝ) (w Ew : HSpace c MeridC) : Prop :=
  ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (fromWt (periodize c (Ew : Profile → MeridC)) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (periodize c (w : Profile → MeridC) p) (pdEta φ p) ∂(cellMeasure c)

/-- Weak `Q_ε = ∂_q - ε(K+1)` on `cellMeasure c` with `Qw = s^{1/2} Q_ε w ∈ H`
(source lines 1646, 1653, 1680, 1790): `Q_ε w = s^{-1/2} Qw`. -/
def WeakQWt (c ε : ℝ) (w Qw : HSpace c MeridC) : Prop :=
  ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (fromWt (periodize c (Qw : Profile → MeridC)) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (periodize c (w : Profile → MeridC) p)
        (pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p)) ∂(cellMeasure c)

/-- **(G_wt) True `s^{1/2}`-weighted gradient transport** (source lines 1680, 1789–1792):
the phase gradient `grad_v` of `v = U (liftVec w)` controls `(s^{1/2} Q_ε w, s^{1/2} ∂_η w)` in `H`
(equivalently `(Q_ε w, ∂_η w)` in `H_T = L²(s^{-1/2} ds dq dη)`). -/
def PhaseGradTransportWt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν c ε : ℝ), 0 < ν → ∀ (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
      ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
      ∀ (w : HSpace c MeridC) (v : D P ν 2) (grad_v : Fin 3 → Yq P 2),
        (v : Yq P 2) = U (B0223.liftVec hε hc hP w) →
        HasGrad (v : Yq P 2) grad_v →
        ∃ Qw Ew : HSpace c MeridC, WeakQWt c ε w Qw ∧ WeakEtaWt c w Ew ∧
          ‖Qw‖ + ‖Ew‖ ≤ C * (‖(v : Yq P 2)‖ + ∑ j : Fin 3, ‖grad_v j‖)

/-- **(P_wt) Cutoff product rule for `(WeakS, WeakQWt, WeakEtaWt)`**: on `supp χ ⊆ {σ ≤ s ≤ H₁}`,
`s^{-1/2} ≤ σ^{-1/2} ≤ 1 + σ⁻¹ ≤ Γ`, giving `HasLocalSQE` with polynomial `Γ` bound. -/
def PhaseCutoffProductRuleWt : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → 0 < c →
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs → 0 ≤ M →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (w Sw Qw Ew : HSpace c MeridC),
        N05_1_1Org.WeakS c w Sw → WeakQWt c ε w Qw → WeakEtaWt c w Ew →
        ∃ u Su Qu Eu : Profile → MeridC,
          HasLocalSQE c σ H1 L1 ε (mulChi (measureH c) χ hm hB w) u Su Qu Eu ∧
          cellL2Norm c u + cellL2Norm c Su + cellL2Norm c Qu + cellL2Norm c Eu ≤
            C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * (‖w‖ + ‖Sw‖ + ‖Qw‖ + ‖Ew‖)

/-- Assembly of `PhaseD2CutoffSQE` from `PhaseGradTransportWt`, `PhaseGeneratorTransport`, and
`PhaseCutoffProductRuleWt`. -/
theorem phaseD2CutoffSQE_of_wt (hG : PhaseGradTransportWt) (hT : N05_1_1Org.PhaseGeneratorTransport)
    (hP' : PhaseCutoffProductRuleWt) : PhaseD2CutoffSQE := by
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

end N05_1_1G

end UnforcedLeray.Short.PartIIa
