import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# `PartIII-a:T21/2/7/2/2/1`: decomposition of `AdjointIntegratedH1`

Source: `the November 2 reference manuscript`
(SP) lines 3060-3067 (cutoff `E_0` energy identity and its integral), 3044-3049 (weight
log-derivatives), 3052-3058 (localized term).  Route: (1) the weighted `L²` energy of the weak
adjoint is bounded on `[t, s]` (strong continuity); (2) for the cutoff `ladCut R` the cutoff
energy identity `E_R' = 2ν ∫ χ_R² jb^{-m} |∇φ|² + errors` with errors `≤ ν ∫ χ_R² jb^{-m}|∇φ|²
+ C (sup E_0 + M²)` integrates on `[r, s']` to a bound uniform in `R` and `s'`; (3) `R → ∞`
(Fatou, `ladCut (n+1)² ↑ 1`) and `s' → s` (monotone).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The common hypotheses of `AdjointIntegratedH1` (SP 3060-3067). -/
def AdjIntCtx (m ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (G : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  0 < ν ∧ ν ≤ 1 ∧ (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) ∧ 0 ≤ t ∧ t < s ∧
    MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) ∧
    IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)

/-- The cutoff gradient energy `∫ χ_R² jb^{-m} |∂_kφ(ρ)|²` (SP 3060-3067), `χ_R = ladCut R`. -/
def cutGradEnergy (c m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (k : Fin 2) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ladCut R x ^ 2) * ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
    ∂(B0579.cellMeasure c (-m))

/-- **(1) Uniform weighted `L²` bound** (SP 3060, strong continuity of the weak adjoint on the
compact `[t, s]`): `‖φ ρ‖²_{X_{-m,c}} ≤ M` for `ρ ∈ [t, s]`. -/
def AdjSupL2 (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ →
    ∃ M : ℝ, ∀ ρ ∈ Icc t s,
      ∫⁻ x, ‖φ ρ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M

/-- **(2) Cutoff energy integral, uniform in `R` and `s'`** (SP 3060-3067: `E_R' = 2ν ∫ χ_R²
jb^{-m}|∇φ|² + errors`, errors `≤ ν ∫ χ_R² jb^{-m}|∇φ|² + C(sup E_0 + M²)` where
`|∇jb^{-m}| ≤ 2|m| jb^{-m}`, `|∇χ_R| ≤ K/R`, `|v| ≤ C` (`LadTrainBdd`), `χ = ladChi` bounded
(`adjWeakChiBound`); integrate on `[r, s']`): given the `L²` bound `M`, there is `K` with
`ν ∑_k ∫_r^{s'} ∫ χ_R² jb^{-m}|∂_kφ|² ≤ K` for all `R ≥ 1`, `t ≤ r ≤ s' < s`. -/
def AdjCutRate (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ M : ℝ,
    (∀ ρ ∈ Icc t s,
      ∫⁻ x, ‖φ ρ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M) →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ r ∈ Ico t s, ∀ s' ∈ Ico r s,
      ENNReal.ofReal ν * ∑ k : Fin 2,
        ∫⁻ ρ in Ioc r s', cutGradEnergy (ν ^ (-2 : ℝ)) m R φ k ρ ≤ ENNReal.ofReal K

/-- **(3) Limit passage** (SP 3060-3067): a bound uniform in `R ≥ 1` and `s' < s` for the cutoff
energies gives finiteness of the uncut integral (Fatou for `R → ∞` along `ladCut (n+1)² ↑ 1`,
then monotone convergence for `s' ↑ s`; measurability from joint smoothness on `[t, s)`). -/
def AdjCutLimit (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ K : ℝ,
    (∀ R : ℝ, 1 ≤ R → ∀ r ∈ Ico t s, ∀ s' ∈ Ico r s,
      ENNReal.ofReal ν * ∑ k : Fin 2,
        ∫⁻ ρ in Ioc r s', cutGradEnergy (ν ^ (-2 : ℝ)) m R φ k ρ ≤ ENNReal.ofReal K) →
    ∀ r ∈ Ico t s, ∀ k : Fin 2,
      ∫⁻ ρ in Ioc r s, (∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
        ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤

/-- `AdjointIntegratedH1` from the three steps. -/
theorem adjointIntegratedH1_of (m : ℝ) (h1 : AdjSupL2 m) (h2 : AdjCutRate m)
    (h3 : AdjCutLimit m) : AdjointIntegratedH1 m := by
  intro ν hν hν1 tr hb t s ht hts G hG φ hφ hs
  have hctx : AdjIntCtx m ν tr t s G φ := ⟨hν, hν1, hb, ht, hts, hG, hφ, hs⟩
  obtain ⟨M, hM⟩ := h1 ν tr t s G φ hctx
  obtain ⟨K, hK⟩ := h2 ν tr t s G φ hctx M hM
  exact h3 ν tr t s G φ hctx K hK

end UnforcedLeray.Short.IIIa
