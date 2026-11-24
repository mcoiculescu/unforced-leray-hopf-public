import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIb.NearProofs

/-!
# The actual forced column (source 4079-4132): statements of the steps

Source of record: `the November 2 reference manuscript`.  With the body inverses
`R_ε, R_0` (real forms of `T_ε, T_0`, `IsBodyTransport`), `u_ε = M_U R_ε f`, `u_0 = M_0 R_0 f`,
`T_ε = D_N⁻¹u_ε`, `T_0 = D_0⁻¹u_0`, the resolvent identity (4126-4132, `forcedColumnComparison`)
`G⁻¹(T_ε - T_0) = (G⁻¹D_N⁻¹G)(G⁻¹(u_ε - u_0)) + (G⁻¹(D_N⁻¹ - D_0⁻¹)G)(G⁻¹u_0)` reduces
`ForcedColumnC` (`NearInst/Targets.lean`) to `NearSolverC` and the two column statements:

* `FlatBodyColumnBound` : `‖g⁻¹u_0‖_Z ≤ P_ν‖f‖_H` (4116-4119: `g⁻¹ ≤ 1`, the flat train multiplier,
  the free body bound `‖T_0‖ ≤ (μ + 1/4)⁻¹`).
* `BodyColumnComparison` : `‖g⁻¹(u_ε - u_0)‖_Z ≤ P_ν e^{-c/ν}‖f‖_H` (4119-4124).

`BodyColumnComparison` splits as `u_ε - u_0 = (M_U - M_0)R_εf + M_0(R_ε - R_0)f`:

* `BodyCoeffColumn` : the coefficient difference (4032-4036 thin: `P_ν ε e^{m₀/ν}`, via the
  inlet columns `|α_i| ≤ ρ_b`; 4045-4049 broad: `2√ρ_b`), on any input.
* `BodyGeomColumn` : the geometric difference with the train multiplier, output split into the
  window box `ε^a ≤ s < ε^{-b}`, `|η| ≤ L_⊥` and its complement (the end regions `s < s₋`,
  `s ≥ S` and the transverse tail, 3962-3969, 4011-4020: train bounds `P_ν√s₋`,
  `P_ν(S^{-1/2} + ε)`, `e^{-D/ν}`).
* `BodyWindowComparison` : on the window box, the body clause of
  `PartIIa.NearCompactFreeComparison` (1692-1722, rate `ε^{1/14}`) in real form, with
  `Γ^K ≤ P_ν ε^{-K(a+b)}` (3962-3967).

Leaf statements: `GainInvContract` (`g⁻¹ ≤ 1`, 4092), `BodyFormNorm` (norm of a real form),
`WindowCutoffExists` (smooth window cutoffs with polynomial `C⁸` norms, the `χ, χ₁` of
`near:compact-free-comparison`, 1695-1702).  Reused: `NearSolverC`, `FlatTrainMultBound`
(`Targets.lean`); `Delta.TrainMultRestr`, `Delta.ThinDiffMult`, `Delta.BroadMult`,
`Delta.RawStreamCompletion`, `Delta.RepairCoeffBound` (`Delta/Lemmas.lean`);
`IIIa.RawCoeffEarly`, `IIIa.RawCoeffLate`, `IIIa.InletCoeffBounds`, `IIIa.RawTransverseTail`
(`PartIII-a/StressInputs.lean`); `PartIIa.NearCompactFreeComparison`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

/-! ## Leaf statements -/

/-- **The inverse gain is a contraction** (source 4092, 4116-4118: for `γ ≥ 0`,
`g = e^{γs/(1+νs)} ≥ 1`, so multiplication by `g⁻¹` does not increase the norms of `H` and `Z`). -/
def GainInvContract : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν), 0 ≤ γ →
    (∀ u : Hsp c, ‖(gainH c γ hν).symm u‖ ≤ ‖u‖) ∧
      ∀ F : Zsp c mZ ρb, ‖(gainEquiv c mZ ρb γ hν).symm F‖ ≤ ‖F‖

/-- **The norm of a real form** (source 1641-1646, 2676-2679: the two normalisations `dq` and
`dq/c` of the velocity measure multiply all norms by the same factor `√c`, so a real form `R` of
a complex body operator `R'` has `‖R f‖ ≤ ‖R'‖ ‖f‖`). -/
def BodyFormNorm : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (R : Hsp c →L[ℝ] Hsp c) (R' : HSpace c MeridC →L[ℂ] HSpace c MeridC),
    IsBodyTransport R R' → ∀ f : Hsp c, ‖R f‖ ≤ ‖R'‖ * ‖f‖

/-- **Window cutoffs** (source 1695-1702: `χ` supported in `σ ≤ s ≤ H₁`, `|η| ≤ L₁`, `χ₁ = 1` on a
larger neighbourhood, `‖χ‖_{C⁸}, ‖χ₁‖_{C⁸}` entering `Γ`; 3962-3967: the window `[s₋, S]` and the
transverse box `L_⊥`).  There are `C, k` such that for `0 < σ ≤ H` and `L ≥ 0` there is a smooth
`q`-periodic cutoff `χ`, `|χ| ≤ 1`, equal to one on `σ ≤ s ≤ H`, `|η| ≤ L`, supported in
`σ/2 ≤ s ≤ 2H`, `|η| ≤ 2L + 1`, with a larger cutoff `χ₁`, and
`‖χ‖_{C⁸} + ‖χ₁‖_{C⁸} ≤ C (σ⁻¹ + H + L + 2)^k`. -/
def WindowCutoffExists : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ c σ H L : ℝ, 0 < c → 0 < σ → σ ≤ H → 0 ≤ L →
    ∃ χ χ1 : Profile → ℝ,
      UnforcedLeray.Short.PartIIa.IsNearCutoff c (σ / 2) (2 * H) (2 * L + 1) χ ∧
      UnforcedLeray.Short.PartIIa.IsLargerCutoff c χ χ1 ∧ Measurable χ ∧ (∀ p, |χ p| ≤ 1) ∧
      (∀ p : Profile, σ ≤ p.1 → p.1 ≤ H → |p.2.2| ≤ L → χ p = 1) ∧
      UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
        C * (σ⁻¹ + H + L + 2) ^ k

/-! ## The window comparison (source 1692-1722, 3956-3967) -/

/-- **The body comparison on the window box** (source 1692-1722, first rate of
`near:compact-free-rates`: `‖χ(T_ε - T_0)‖_{H→H} ≤ CΓ^kε^{1/14}`; 3962-3967: with
`s₋ = ε^a`, `S = ε^{-b}`, `L_⊥ = C_⊥(c/ν + √S + 1)`, `Γ^K ≤ P_ν ε^{-K(a+b)}`).  For
`K ⋐ (0, 1/4)` and the window `[d₋, d₊]` there is a fixed integer `K` such that for `a, b, C_⊥`:
at every level of the regime with `ν ≤ ν₀`, every `μ ∈ K` and every pair of real forms `R_ε, R_0`
of `T_ε, T_0`, the output restriction to the box `ε^a ≤ s < ε^{-b}`, `|η| ≤ L_⊥` satisfies
`‖1_{box}(R_ε - R_0)f‖_H ≤ C ν^{-k} ε^{1/14-K(a+b)} ‖f‖_H`.
Route: a window cutoff `χ = 1` on the box (`WindowCutoffExists`, `σ = ε^a`, `H = ε^{-b}`,
`L = L_⊥`), so `1_{box} ≤ χ`; the transports `merC ∘ · ∘ cellPt` change norms by `√c` in both
directions (`Masked.CellPtH`, `Masked.CellPtInvH`); `Γ` is polynomial in `ν⁻¹` and `ε^{-(a+b)}`
(`c = ν⁻²`, `sup|μ| ≤ 1/4`, `γ_* ≥ 1/4`); `P = 2εc ≤ 1`, `ε ≤ 1` for small `ν`. -/
def BodyWindowComparison : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b Cperp : ℝ, 0 < a → 0 < b → b < 1 →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset, ∀ Reps R0 : Hsp p.c →L[ℝ] Hsp p.c,
        IsBodyTransport Reps
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) →
        IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) →
        ∀ f : Hsp p.c,
          ‖Delta.outRestr p.c
              (Delta.binSet (p.ε ^ a) (p.ε ^ (-b)) (Delta.transL Cperp p.c p.ν (p.ε ^ (-b))))
              ((Reps - R0) f)‖ ≤
            C * p.ν⁻¹ ^ k * p.ε ^ (1 / 14 - (K : ℝ) * (a + b)) * ‖f‖

/-! ## The two parts of `u_ε - u_0` (source 4032-4049, 4119-4124) -/

/-- **The coefficient difference on the column** (source 4032-4036: the exact thin coefficient
differs from the flat train by the `ε` stream completion and the entrance adjustment `E_ε α`,
`|α_i| ≤ ρ_b`, of multiplier norm `P_ν(ε + ρ_b)`; 4045-4049 and 2766-2769: the broad repair
coupling `2√ρ_b`; `g⁻¹ ≤ 1` on the input, 4116-4118).  For `m_Z > 3/2`, `m₀`, `C₀ > 0`, `k₀`: at
every level of the regime with `ν ≤ ν₀`, every exact split with `ρ_b = rhoB p m₀ C₀ k₀`, every
`γ ≥ 0` and the pinned multipliers, `‖G⁻¹(M_U - M_0)x‖_Z ≤ C ν^{-k}(ε + ρ_b + √ρ_b)‖x‖_H`.
Route: `fstZ + sndZ = id`; `Delta.ThinDiffMult` with the bound of `Delta.RawStreamCompletion` and
`IIIa.InletCoeffBounds` (as `hBth` in `Delta/Assembly.lean`), `Delta.BroadMult` with
`Delta.RepairCoeffBound`, and `G⁻¹M x = gainConjM γ M (g⁻¹x)`, `‖g⁻¹x‖ ≤ ‖x‖`.
The slow age `Σ > 0` and the growing eigenpair `(λ, q)` of the inlet are fixed before the
constants, at the levels with `p.ageCut = Σ`, `p.mode = q` (2048-2049, 2347-2358; the constants of
`IIIa.InletCoeffBounds` depend on them). -/
def BodyCoeffColumn : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ (m0 C0 : ℝ) (k0 : ℕ), 0 < C0 →
    ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
      UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
      ∀ γ : ℝ, 0 ≤ γ →
      ∀ M0 MU : Hsp p.c →L[ℝ] Zsp p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsFlatMult M0 p.trainData → IsSplitMult MU p.R V rb → ∀ x : Hsp p.c,
          ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν_pos).symm
              ((MU - M0) x)‖ ≤
            C * p.ν⁻¹ ^ k * (p.ε + UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 +
              Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0)) * ‖x‖

/-- **The geometric difference on the column** (source 4119-4122: "the body version of the same
output comparison, with rate `ε^{1/14}`, and the coefficient/end-region bounds"; 3962-3969 and
4011-4020).  For `K ⋐ (0, 1/4)`, `m_Z > 3/2` and the window `[d₋, d₊]` there is a fixed integer `K`
such that for `a, b` (`0 < b < 1`) and `D > 0`: at every level of the regime with `ν ≤ ν₀`, every
`ρ_b > 0`, `γ ≥ 0`, `μ ∈ K`, the flat multiplier `M_0` and real forms `R_ε, R_0` of `T_ε, T_0`,
`‖G⁻¹M_0(R_ε - R_0)f‖_Z ≤ C ν^{-k}(ε^{a/2} + ε^{b/2} + ε + e^{-D/ν} + ε^{1/14-K(a+b)})‖f‖_H`.
Route: `w = (R_ε - R_0)f = 1_{box}w + 1_{boxᶜ}w`, the box `binSet ε^a ε^{-b} L_⊥` with
`L_⊥ = transL C_⊥ c ν ε^{-b}`, `C_⊥` from `IIIa.RawTransverseTail` at `D`; on `boxᶜ ⊆ {s < ε^a} ∪
{s ≥ ε^{-b}} ∪ tailSet`, `Delta.TrainMultRestr` with the train bounds of `IIIa.RawCoeffEarly`,
`IIIa.RawCoeffLate`, `IIIa.RawTransverseTail`, `Delta.RawStreamCompletion` (as `hBY`, `hBO`, `hBT`
in `Delta/Assembly.lean`) and `‖w‖ ≤ 8‖f‖` (`BodyFormNorm`, `‖T_ε‖, ‖T_0‖ ≤ (μ + 1/4)⁻¹ ≤ 4`); on
the box, `FlatTrainMultBound` and `BodyWindowComparison`; `GainInvContract` for `g⁻¹`. -/
def BodyGeomColumn : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ →
    ∀ dm dp : ℝ, 0 < dm → ∃ K : ℕ, ∀ a b D : ℝ, 0 < a → 0 < b → b < 1 → 0 < D →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb γ : ℝ, 0 < ρb → 0 ≤ γ → ∀ μ ∈ Kset, ∀ M0 : Hsp p.c →L[ℝ] Zsp p.c mZ ρb,
        IsFlatMult M0 p.trainData → ∀ Reps R0 : Hsp p.c →L[ℝ] Hsp p.c,
        IsBodyTransport Reps
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) →
        IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) →
        ∀ f : Hsp p.c,
          ‖(gainEquiv p.c mZ ρb γ p.ν_pos).symm (M0 ((Reps - R0) f))‖ ≤
            C * p.ν⁻¹ ^ k * (p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε + Real.exp (-D / p.ν) +
              p.ε ^ (1 / 14 - (K : ℝ) * (a + b))) * ‖f‖

/-! ## The two column statements (source 4116-4124) -/

/-- **The flat column** (source 4116-4119: `u_0 = M_0R_0f`, the `H` norm of the fixed force a
viscosity polynomial, no gain on the input, `g⁻¹ ≤ 1`): for `K ⋐ (0, 1/4)`, `m_Z > 3/2`: at every
level of the regime with `ν ≤ ν₀`, every `ρ_b > 0`, `γ ≥ 0`, `μ ∈ K`, the flat multiplier and a
real form `R_0` of `T_0`, `‖G⁻¹M_0R_0f‖_Z ≤ C ν^{-k}‖f‖_H`.
Route: `GainInvContract`; `Delta.TrainMultRestr` on `univ` with `FlatTrainMultBound`
(`G⁻¹M_0x = gainRestrM γ univ M_0 (g⁻¹x)`); `BodyFormNorm` with
`‖T_0‖ ≤ ‖R_0(μ)‖‖P_0‖ ≤ (μ + 1/4)⁻¹` (`B0225.norm_R0_le`, `Submodule.starProjection_norm_le`). -/
def FlatBodyColumnBound : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ →
    ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb γ : ℝ, 0 < ρb → 0 ≤ γ → ∀ μ ∈ Kset, ∀ M0 : Hsp p.c →L[ℝ] Zsp p.c mZ ρb,
        IsFlatMult M0 p.trainData → ∀ R0 : Hsp p.c →L[ℝ] Hsp p.c,
        IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) →
        ∀ f : Hsp p.c, ‖(gainEquiv p.c mZ ρb γ p.ν_pos).symm (M0 (R0 f))‖ ≤ C * p.ν⁻¹ ^ k * ‖f‖

/-- **The column comparison** (source 4119-4124: "the body version of the same output comparison,
with rate `ε^{1/14}`, and the coefficient/end-region bounds above give
`‖g⁻¹(u_ε - u_0)‖_Z ≤ P_ν e^{-c/ν}` for some fixed `c > 0`").  For `K ⋐ (0, 1/4)`, `m_Z > 3/2` and
the window `[d₋, d₊]` there is a fixed integer `K` such that for `a, b` with `0 < b < 1`,
`K(a+b) < 1/14`, `0 < m₀ < 3d₋/11` and `C₀ > 0, k₀` there are `c' > 0` and `C, k, ν₀` with: at every
level of the regime with `ν ≤ ν₀`, every exact split with `ρ_b = rhoB p m₀ C₀ k₀`, every `γ ≥ 0`,
`μ ∈ K`, the pinned multipliers and real forms `R_ε, R_0`,
`‖G⁻¹(M_U R_ε f - M_0 R_0 f)‖_Z ≤ C ν^{-k} e^{-c'/ν}‖f‖_H`.
Route: `M_UR_ε - M_0R_0 = (M_U - M_0)R_ε + M_0(R_ε - R_0)`; `BodyCoeffColumn` with `‖R_εf‖ ≤ 4‖f‖`
(`BodyFormNorm`, `B0223.norm_RepsVec_le`), `BodyGeomColumn` at `D = d₋`; every term is
`P_ν e^{-c'/ν}` since `ε = e^{-d/ν}`, `d ≥ d₋`, `ρ_b = C₀ν^{-k₀}e^{(m₀ - 3d/11)/ν}`,
`c' = min{a d₋/2, b d₋/2, d₋, (1/14 - K(a+b)) d₋, 3d₋/22 - m₀/2}`.
The slow age `Σ > 0` and the growing eigenpair `(λ, q)` of the inlet are fixed before the
constants, at the levels with `p.ageCut = Σ`, `p.mode = q` (as in `BodyCoeffColumn`). -/
def BodyColumnComparison : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ →
    ∀ dm dp : ℝ, 0 < dm → ∃ K : ℕ, ∀ a b m0 : ℝ, 0 < a → 0 < b → b < 1 →
      (K : ℝ) * (a + b) < 1 / 14 → 0 < m0 → m0 < 3 * dm / 11 → ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 →
      ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
        UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (c' C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < c' ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
      ∀ γ : ℝ, 0 ≤ γ → ∀ μ ∈ Kset,
      ∀ M0 MU : Hsp p.c →L[ℝ] Zsp p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsFlatMult M0 p.trainData → IsSplitMult MU p.R V rb →
      ∀ Reps R0 : Hsp p.c →L[ℝ] Hsp p.c,
        IsBodyTransport Reps
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) →
        IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) →
        ∀ f : Hsp p.c,
          ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν_pos).symm
              (MU (Reps f) - M0 (R0 f))‖ ≤
            C * p.ν⁻¹ ^ k * Real.exp (-c' / p.ν) * ‖f‖

end UnforcedLeray.Short.PartIIIb.NearInst.Body
