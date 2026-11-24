import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1

/-!
# `PartIII-a:T21/2/7/2/2/1/2`: decomposition of `AdjCutRate`

Source: `the November 2 reference manuscript`
(SP) lines 3060-3067 (cutoff `E_0` energy identity and its integral), 3044-3049 (weight
log-derivatives `|∇ jb^{-m}| ≤ 2|m| jb^{-m}`), 3052-3058 (`χ` bounded in `X_{-m}`).

Route: for `E_R(ρ) = ∫ χ_R² jb^{-m} |φ ρ|²` (the cutoff `L²` energy):
(a) `E_R' = D_R = 2 ∫ χ_R² jb^{-m} Re(conj φ ∂_ρ φ)` on `(t, s)`;
(b) `E_R`, `D_R`, `G_k^R = ∫ χ_R² jb^{-m} |∂_kφ|²` are continuous on `[t, s)`;
(c) `D_R ≥ ν ∑_k G_k^R - K` (use `∂_ρφ = χ - νΔφ - v·∇φ`, one integration by parts, Young,
    `|∇χ_R| ≤ K/R`, `|v| ≤ C`, `‖χ‖_{X_{-m}} ≤ M_χ`, `E_0 ≤ M`);
(d) integrate on `[r, s']` (FTC) and use `E_R(s') ≤ E_0(s') ≤ M`, `E_R(r) ≥ 0`;
(e) convert the real integrals to the `lintegral` form of `AdjCutRate`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The cutoff `L²` energy `E_R(ρ) = ∫_{C_c} χ_R² jb^{-m} |φ ρ|²` (SP 3060-3067). -/
def cutE0 (c m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) : ℝ :=
  ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)

/-- The cutoff gradient energy density, real form: `G_k^R(ρ) = ∫ χ_R² jb^{-m} |∂_kφ ρ|²`. -/
def cutGReal (c m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (k : Fin 2) (ρ : ℝ) : ℝ :=
  ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (φ ρ) x‖ ^ 2)

/-- The formal rate `D_R(ρ) = 2 ∫ χ_R² jb^{-m} Re(conj φ · ∂_ρφ)` of `E_R`. -/
def cutE0Rate (c m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) : ℝ :=
  2 * ∫ x in B0579.cell c,
    ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (φ ρ x) * ladDt φ ρ x).re)

/-- **(a) Differentiation under the integral** (calculus on the compact band `supp χ_R`): `E_R' = D_R`
on `(t, s)`. -/
def AdjCutE0Deriv (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ R : ℝ, 0 < R →
    ∀ ρ ∈ Ioo t s,
      HasDerivAt (cutE0 (ν ^ (-2 : ℝ)) m R φ) (cutE0Rate (ν ^ (-2 : ℝ)) m R φ ρ) ρ

/-- **(b) Continuity in `ρ` on `[t, s)`** of `E_R`, `D_R` and `G_k^R` (joint smoothness of `φ` on
`[t, s) × ℝ²` and the compact support of `χ_R`). -/
def AdjCutE0Cont (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ R : ℝ, 0 < R →
    ContinuousOn (cutE0 (ν ^ (-2 : ℝ)) m R φ) (Ico t s) ∧
    ContinuousOn (cutE0Rate (ν ^ (-2 : ℝ)) m R φ) (Ico t s) ∧
    ∀ k : Fin 2, ContinuousOn (cutGReal (ν ^ (-2 : ℝ)) m R φ k) (Ico t s)

/-- **(c) Lower bound for the rate** (SP 3060-3067: insert `∂_ρφ = χ - νΔφ - v·∇φ`, integrate the
Laplacian by parts once in `x` (the seam terms cancel by periodicity), Young on the cross terms,
`|∇(χ_R² jb^{-m})| ≤ K₂ χ_R jb^{-m}`, `|v| ≤ C` (`LadTrainBdd`), `χ` bounded in `X_{-m}`
(`adjWeakChiBound`, `m > 8`), `E_0 ≤ M`): `D_R ≥ ν ∑_k G_k^R - K` on `(t, s)`, `K` independent
of `R ≥ 1`. -/
def AdjCutE0Lower (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ M : ℝ, 8 < m →
    (∀ ρ ∈ Icc t s,
      ∫⁻ x, ‖φ ρ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M) →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t s,
      ν * ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ - K ≤
        cutE0Rate (ν ^ (-2 : ℝ)) m R φ ρ

/-- **(d) Integrated real bound** (FTC on `[r, s']` with (a)-(c), `E_R(s') ≤ M` via
`integral_cellMeasure_eq` and `ladCut ≤ 1`, `E_R(r) ≥ 0`): there is `K` with
`ν ∑_k ∫_r^{s'} G_k^R ≤ K` for all `R ≥ 1`, `t ≤ r ≤ s' < s`. -/
def AdjCutRateReal (m : ℝ) : Prop :=
  AdjCutE0Deriv m → AdjCutE0Cont m → AdjCutE0Lower m → 8 < m →
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ M : ℝ,
    (∀ ρ ∈ Icc t s,
      ∫⁻ x, ‖φ ρ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M) →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ r ∈ Ico t s, ∀ s' ∈ Ico r s,
      ν * ∑ k : Fin 2, ∫ ρ in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ ≤ K

/-- **(e) Conversion to `lintegral` form**: `cutGradEnergy = ofReal (cutGReal)` (via
`integral_cellMeasure_eq`, `lintegral` of the nonnegative continuous integrand over the cell),
`∫⁻_{Ioc r s'} ofReal G = ofReal ∫_r^{s'} G` for `G ≥ 0` continuous on `[r, s']`
(`ofReal_integral_eq_lintegral_ofReal`), and the sum over `k` into `ofReal`. -/
def AdjCutConvert (m : ℝ) : Prop :=
  AdjCutE0Cont m →
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjIntCtx m ν tr t s G φ → ∀ K : ℝ,
    (∀ R : ℝ, 1 ≤ R → ∀ r ∈ Ico t s, ∀ s' ∈ Ico r s,
      ν * ∑ k : Fin 2, ∫ ρ in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ ≤ K) →
    ∀ R : ℝ, 1 ≤ R → ∀ r ∈ Ico t s, ∀ s' ∈ Ico r s,
      ENNReal.ofReal ν * ∑ k : Fin 2,
        ∫⁻ ρ in Ioc r s', cutGradEnergy (ν ^ (-2 : ℝ)) m R φ k ρ ≤ ENNReal.ofReal K

/-- `AdjCutRate` from the leaves (a)-(e). -/
theorem adjCutRate_of (m : ℝ) (hm : 8 < m) (h1 : AdjCutE0Deriv m) (h2 : AdjCutE0Cont m)
    (h3 : AdjCutE0Lower m) (h4 : AdjCutRateReal m) (h5 : AdjCutConvert m) : AdjCutRate m := by
  intro ν tr t s G φ hctx M hM
  obtain ⟨K, hK⟩ := h4 h1 h2 h3 hm ν tr t s G φ hctx M hM
  exact ⟨K, fun R hR r hr s' hs' =>
    h5 h2 ν tr t s G φ hctx K hK R hR r hr s' hs'⟩

end UnforcedLeray.Short.IIIa
