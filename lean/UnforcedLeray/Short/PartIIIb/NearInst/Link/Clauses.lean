import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# The near clauses of the return layer (source 5536-5547, 4079-4132, 5891-5899)

Source of record: `the November 2 reference manuscript` (73 pages).

Over a `Concrete.ReturnBase` linked to the concrete near operators (`IsNearLinked`,
`IsBodyLinked`, `NearInst/Link/Agree.lean`):

* `NearClausesC` : the near clauses of `PairNormAndNearSolver` (`StatementsA.lean`, source
  5540-5547 with 5657-5658) at one regime, with constants uniform over the regime:
  `‖D_N⁻¹T‖ ≤ P_ν‖T‖`, `‖S_N T‖ ≤ P_ν e^{η_δ/ν}‖T‖` in the gain norms, and the pair norm.
  **Proved** here from `NearSolverC` (`nearClausesC_of`).
* `BodyColumnC` : the body-column comparison on the return spaces,
  `‖D_N⁻¹M R_μ f - T₀f‖_Str ≤ P_ν e^{-c'/ν}‖f‖_Src` (source 4109-4118, the near input of
  `CurvedFlatComparison`, 5891-5899).  **Proved** here from `ForcedColumnC` (`bodyColumnC_of`).
* `IsFlatColumnKflat` : the pin `𝒦^flat = 𝓛𝔗`, `𝔗A = T₀F_A` the flat forced column of the same
  prescribed affine force (source 4761-4763, 4804-4806, 4109-4111, 5897-5899), and
  `curvedFlat_le` : `‖L𝒫 - 𝒦^flat‖ ≤ ‖𝓛‖ · (column bound) · ‖F‖` (source 5891-5899).
* Pin derivations (tasks): `MultLinkOf` (`IsExactMultiplier` and `IsSplitMult` give
  `B.M = o.MG`), its converse `MultPinOfLink`, and `NearLinkOf` (`NearSNAgree` gives
  `B.SN = o.SNG`).  A return base may also be *built* from the near operators:
  `M := o.MG`, `SN := o.SNG`, `DNinv := o.DNinvG` with `NearOps.DNinvG_left/right`
  (`NearInst/Link/Agree.lean`, `IsUnit o.DN` from `NearSolverC`); then `IsNearLinked` is `⟨rfl, rfl⟩`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-! ## 1. Pin derivations -/

/-- **The multiplier link from the two multiplier pins** (source 2706, 3876-3878, 5779-5782): the
exact multiplier of the return base (`Concrete.IsExactMultiplier`, gain-weighted measures) and the
split multiplier `M_U` of the near layer (`IsSplitMult`, ungained measures) are the same pointwise
formula `(v⊗w + w⊗v, v_b⊗w + w⊗v_b)`, so `B.M = o.MG γ hν`. -/
def MultLinkOf : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (Aff : Type) [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb) (R : ℝ)
    (V rb : ℝ → UnforcedLeray.SpatialField),
    IsExactMultiplier B R V rb → IsSplitMult o.MU R V rb → B.M = o.MG γ hν

/-- **The near-inverse link from the function-level agreement** (`Concrete.NearSNAgree`, source
3888-3920): if `B.SN` and `o.SN` agree on stresses with the same sum `T₁ + T₂`, then
`B.SN = o.SNG γ hν` (`ρ_b > 0`, so that `ρ_b^{-1/2}H_T` sees all null sets of `H_T`). -/
def NearLinkOf : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν), 0 < ρb → ∀ (Aff : Type) [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb),
    NearSNAgree B o → B.SN = o.SNG γ hν

/-- **The multiplier pin from the link** (source 2706, 3876-3878, 5779-5782; converse of
`MultLinkOf`): a return base whose multiplier is defined as `o.MG` for a split multiplier `o.MU`
satisfies the exact-multiplier pin of the physical layer. -/
def MultPinOfLink : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (Aff : Type) [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb) (R : ℝ)
    (V rb : ℝ → UnforcedLeray.SpatialField),
    IsSplitMult o.MU R V rb → B.M = o.MG γ hν → IsExactMultiplier B R V rb

/-! ## 2. The near clauses (source 5536-5547) -/

/-- **The near clauses of `PairNormAndNearSolver` at one regime** (source 5540-5547, 5657-5658),
under the parameter choice of `NearSolverC` (4109-4124): for every return base linked to the actual
near operators, `‖D_N⁻¹T‖_Str ≤ P_ν‖T‖_Str`, `‖S_N T‖_Vel ≤ P_ν e^{η_δ/ν}‖T‖_Str`
(`η_δ = γ tanh(3δ/8)`), and the pair norm `‖V‖ = ‖T‖ + e^{-γ/(8ν)}‖w‖` of `𝓔_ν`.  As in
`NearSolverC`, the slow age `Σ > 0` of the inlet is fixed before the constants, at the levels with
`p.ageCut = Σ`, `p.mode = P.mode` (2048-2049, 2347-2358). -/
def NearClausesC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ m0 Dp : ℝ, 0 < a → 0 < b → b < 1 → (K : ℝ) * (a + b) < 1 / 100 → 0 < δ →
      0 < m0 → m0 < 3 * dm / 11 →
      etaDelta P.eigenvalue.re δ < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      m0 < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      etaDelta P.eigenvalue.re δ + thetaAB a b * (P.eigenvalue.re / 3) < Dp →
      ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 → ∀ c₁ c₂ rmax : ℝ, 0 < c₁ → c₁ ≤ c₂ → 0 ≤ rmax →
      ∀ Sig : ℝ, 0 < Sig →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = P.mode →
      (∃ Cs ∈ Icc c₁ c₂, ∃ r ∈ Icc (-rmax) rmax,
        p.ε = Cs * p.ν ^ r * Real.exp (-(P.eigenvalue.re / 3) / p.ν)) →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
        S_in ≤ p.ε ^ (-b) →
      ∀ μ ∈ Kset, ∀ o : NearOps p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsActualNear p V rb μ δ (p.ε ^ (-b)) o →
      ∀ (Aff : Type) [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
        (B : ReturnBase p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re p.ν Aff),
        IsNearLinked B o p.ν_pos →
        (∀ T, ‖B.toOps.DNinv T‖ ≤ C * p.ν⁻¹ ^ k * ‖T‖) ∧
        (∀ T, ‖B.toOps.SN T‖ ≤
          C * p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * ‖T‖) ∧
        (∀ X : B.Gam, ‖X‖ = ‖B.toOps.Tc X‖ +
          Real.exp (-(P.eigenvalue.re / 8) / p.ν) * ‖B.toOps.wc X‖)

/-- `NearSolverC` gives the near clauses on the return spaces (source 5540-5547). -/
theorem nearClausesC_of (h : NearSolverC) : NearClausesC := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm
  obtain ⟨K, hK'⟩ := h P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨K, ?_⟩
  intro a b δ m0 Dp ha hb hb1 hKab hδ hm0 hm0' hη hm0θ hD C0 k0 hC0 c₁ c₂ rmax hc₁ hc₁₂ hr
    Sig hSig
  obtain ⟨C, k, ν₀, hν₀, hC⟩ :=
    hK' a b δ m0 Dp ha hb hb1 hKab hδ hm0 hm0' hη hm0θ hD C0 k0 hC0 c₁ c₂ rmax hc₁ hc₁₂ hr
      Sig hSig
  refine ⟨max C (Real.sqrt Real.pi * C), k, ν₀, hν₀, ?_⟩
  intro p d hp hpν hSg hmode hε S_in V rb hV hS μ hμ o ho Aff _ _ _ B hB
  obtain ⟨-, -, hDN, -, hSN⟩ := hC p d hp hpν hSg hmode hε S_in V rb hV hS μ hμ o ho
  have hk : 0 ≤ p.ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 p.ν_pos.le) k
  refine ⟨fun T => ?_, fun T => ?_, fun X => B.toOps_pairNorm X⟩
  · show ‖B.DNinv T‖ ≤ _
    rw [hB.dninv_eq]
    calc ‖o.DNinvG P.eigenvalue.re p.ν_pos T‖
        ≤ ‖conjG (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
            p.ν_pos) (Ring.inverse o.DN)‖ * ‖T‖ := o.norm_DNinvG_le _ _ T
      _ ≤ (C * p.ν⁻¹ ^ k) * ‖T‖ := mul_le_mul_of_nonneg_right hDN (norm_nonneg _)
      _ ≤ max C (Real.sqrt Real.pi * C) * p.ν⁻¹ ^ k * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hk)
            (norm_nonneg _)
  · show ‖B.SN T‖ ≤ _
    rw [hB.near]
    have he : 0 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := (Real.exp_pos _).le
    calc ‖o.SNG P.eigenvalue.re p.ν_pos T‖
        ≤ Real.sqrt Real.pi * ‖gainConjS P.eigenvalue.re p.ν_pos o.SN‖ * ‖T‖ :=
          o.norm_SNG_le _ _ T
      _ ≤ Real.sqrt Real.pi *
            (C * p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) * ‖T‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSN (Real.sqrt_nonneg _)) (norm_nonneg _)
      _ = (Real.sqrt Real.pi * C) * p.ν⁻¹ ^ k *
            Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * ‖T‖ := by ring
      _ ≤ max C (Real.sqrt Real.pi * C) * p.ν⁻¹ ^ k *
            Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hk) he) (norm_nonneg _)

/-! ## 3. The body column (source 4079-4118) -/

/-- **The body-column comparison on the return spaces** (source 4109-4118; the near input of
`CurvedFlatComparison`, 5891-5899): under the hypotheses of `ForcedColumnC`, for every return base
linked to the actual near operators and to the curved body inverse `R_ε`, the curved column
`D_N⁻¹M R_μ f` and the flat column `T₀f = D₀⁻¹M₀R₀f` (`flatColG`) differ by
`P_ν e^{-c'/ν}‖f‖_Src` in the gain norm of `Str` (no gain on the input, 4116-4118).  As in
`ForcedColumnC`, the slow age `Σ > 0` of the inlet is fixed before the constants, at the levels
with `p.ageCut = Σ`, `p.mode = P.mode` (2048-2049, 2347-2358). -/
def BodyColumnC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ m0 Dp : ℝ, 0 < a → 0 < b → b < 1 → (K : ℝ) * (a + b) < 1 / 100 → 0 < δ →
      0 < m0 → m0 < 3 * dm / 11 →
      etaDelta P.eigenvalue.re δ < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      m0 < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      etaDelta P.eigenvalue.re δ + thetaAB a b * (P.eigenvalue.re / 3) < Dp →
      ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 → ∀ c₁ c₂ rmax : ℝ, 0 < c₁ → c₁ ≤ c₂ → 0 ≤ rmax →
      ∀ Sig : ℝ, 0 < Sig →
    ∃ (c' C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < c' ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = P.mode →
      (∃ Cs ∈ Icc c₁ c₂, ∃ r ∈ Icc (-rmax) rmax,
        p.ε = Cs * p.ν ^ r * Real.exp (-(P.eigenvalue.re / 3) / p.ν)) →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
        S_in ≤ p.ε ^ (-b) →
      ∀ μ ∈ Kset, ∀ o : NearOps p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsActualNear p V rb μ δ (p.ε ^ (-b)) o →
      ∀ Reps R0 : Hsp p.c →L[ℝ] Hsp p.c,
        IsBodyTransport Reps
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) →
        IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) →
      ∀ (Aff : Type) [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
        (B : ReturnBase p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re p.ν Aff),
        IsNearLinked B o p.ν_pos → IsBodyLinked B Reps p.ν_pos →
        ∀ f : SrcG p.c,
          ‖B.DNinv (B.M (B.R f)) - o.flatColG P.eigenvalue.re p.ν_pos R0 f‖ ≤
            C * p.ν⁻¹ ^ k * Real.exp (-c' / p.ν) * ‖f‖

/-- `ForcedColumnC` gives the body-column comparison on the return spaces (source 4109-4118). -/
theorem bodyColumnC_of (h : ForcedColumnC) : BodyColumnC := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm
  obtain ⟨K, hK'⟩ := h P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨K, ?_⟩
  intro a b δ m0 Dp ha hb hb1 hKab hδ hm0 hm0' hη hm0θ hD C0 k0 hC0 c₁ c₂ rmax hc₁ hc₁₂ hr
    Sig hSig
  obtain ⟨c', C, k, ν₀, hc', hν₀, hC⟩ :=
    hK' a b δ m0 Dp ha hb hb1 hKab hδ hm0 hm0' hη hm0θ hD C0 k0 hC0 c₁ c₂ rmax hc₁ hc₁₂ hr
      Sig hSig
  refine ⟨c', C, k, ν₀, hc', hν₀, ?_⟩
  intro p d hp hpν hSg hmode hε S_in V rb hV hS μ hμ o ho Reps R0 hRe hR0 Aff _ _ _ B hB hBR f
  calc ‖B.DNinv (B.M (B.R f)) - o.flatColG P.eigenvalue.re p.ν_pos R0 f‖
      ≤ ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
          p.ν_pos).symm (Ring.inverse o.DN (o.MU (Reps (srcIso p.c f))) -
            Ring.inverse o.D0 (o.M0 (R0 (srcIso p.c f))))‖ := norm_column_sub_le hB hBR R0 f
    _ ≤ C * p.ν⁻¹ ^ k * Real.exp (-c' / p.ν) * ‖srcIso p.c f‖ :=
        hC p d hp hpν hSg hmode hε S_in V rb hV hS μ hμ o ho Reps R0 hRe hR0 (srcIso p.c f)
    _ = C * p.ν⁻¹ ^ k * Real.exp (-c' / p.ν) * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]

/-! ## 4. The curved loop against the flat return (source 5891-5899) -/

section Curved

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **The flat return is `𝓛` of the flat forced column of the same force** (source 4761-4763,
4804-4806 `𝒦^flat = 𝓛𝔗`, `𝔗A` the complete flat stress of the zero-entrance forced column;
4109-4111 the same prescribed smooth Gaussian affine force in both geometries, 5897-5899): `𝒦^flat =
𝓛 ∘ T₀ ∘ F`, `T₀ = flatColG R₀`. -/
def IsFlatColumnKflat (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb)
    (R0 : Hsp c →L[ℝ] Hsp c) (hν : 0 < ν) : Prop :=
  B.Kflat = B.Lj ∘L o.flatColG γ hν R0 ∘L B.FA

/-- `L𝒫 A = 𝓛(D_N⁻¹M R_μ F_A)` (source 5815-5818: `𝒫A = 𝒥(R_μF_A)`, `L(T,w) = 𝓛T`). -/
theorem Lg_P_apply (B : ReturnBase c mZ ρb γ ν Aff) (A : Aff) :
    (B.toOps.Lg ∘L B.toOps.P) A = B.Lj (B.DNinv (B.M (B.R (B.FA A)))) := rfl

/-- **The curved loop against the flat return** (source 5891-5899): with `𝒦^flat = 𝓛T₀F`, a column
bound `‖D_N⁻¹M R_μ f - T₀f‖ ≤ C_b‖f‖`, `‖𝓛‖ ≤ C_L` and `‖F‖ ≤ C_F`,
`‖L𝒫 - 𝒦^flat‖ ≤ C_L C_b C_F`. -/
theorem curvedFlat_le (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb)
    (R0 : Hsp c →L[ℝ] Hsp c) (hν : 0 < ν) (hK : IsFlatColumnKflat B o R0 hν) {Cb CL CF : ℝ}
    (hCb : 0 ≤ Cb) (hb : ∀ f, ‖B.DNinv (B.M (B.R f)) - o.flatColG γ hν R0 f‖ ≤ Cb * ‖f‖)
    (hL : ‖B.Lj‖ ≤ CL) (hF : ‖B.FA‖ ≤ CF) :
    ‖B.toOps.Lg ∘L B.toOps.P - B.Kflat‖ ≤ CL * Cb * CF := by
  have hCL : 0 ≤ CL := (norm_nonneg _).trans hL
  have hCF : 0 ≤ CF := (norm_nonneg _).trans hF
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
  rw [ContinuousLinearMap.sub_apply, Lg_P_apply, hK, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← map_sub]
  calc ‖B.Lj (B.DNinv (B.M (B.R (B.FA A))) - o.flatColG γ hν R0 (B.FA A))‖
      ≤ ‖B.Lj‖ * ‖B.DNinv (B.M (B.R (B.FA A))) - o.flatColG γ hν R0 (B.FA A)‖ :=
        B.Lj.le_opNorm _
    _ ≤ CL * (Cb * ‖B.FA A‖) := mul_le_mul hL (hb _) (norm_nonneg _) hCL
    _ ≤ CL * (Cb * (CF * ‖A‖)) := by
        gcongr
        exact (B.FA.le_opNorm A).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
    _ = CL * Cb * CF * ‖A‖ := by ring

end Curved

end UnforcedLeray.Short.PartIIIb.NearInst
