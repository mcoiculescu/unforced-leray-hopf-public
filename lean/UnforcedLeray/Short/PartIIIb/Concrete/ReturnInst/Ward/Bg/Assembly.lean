import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Assembly

/-!
# The Ward fields along the sequence without a background hypothesis (source 4161-4303,
5926-5950)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `ORG:return-concrete/instance-3/ward/bg`.  `Ward/Assembly.lean` proves the Ward triple along
the sequence from the leaves and the hypothesis `hbg` (`WardBgBound`, a pointwise bound of `∇p` that
the source does not provide).  Here:

* `wo_isL2Family_HL`, `wo_isL2Family_EL`, `wardTriple_exists_ofL`: the families and the triple at
  one regime from `WardHBoundL`, `WardEBoundL` and `WardBgBoundL` (`Bg/Defs.lean`);
* `seq_wardBgBoundL`: at actual levels (`SeqData.IsActualLevel`: regime, exact split, exact
  profile and the ball datum `ball`, source 2505-2524, 2706-2711) with the growing eigenpair
  `D.Pl.mode`, `WardBgBoundL` holds eventually, from the background facts `BgYoungW2` (2525-2562,
  2607-2609; at the exact split) and `BgPresY2B` (2607-2612, 2641-2642, 5245-5260; at the ball,
  with the slow age `D.Sig` and the ball constants `m₀ > 0`, `2m₀ < 3d₋/11`, `C₀ > 0`, `k₀` of `D.K`,
  as `seq_axi` in `Background/Seq.lean`) and `ν_n → 0` (`retNu_tendsto`);
* `seqWardTriple_exists_ofL`: the Ward triple along the sequence with no background hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The families and the triple at one regime -/

section Families

variable {c mZ ρb γ ν ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {χy : ℝ → ℝ}

/-- **`h[T]` is an `L²` family** in the gained body measure (source 4171-4174, 4194-4195), for a
background with `WardBgBoundL`. -/
theorem wo_isL2Family_HL {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {M : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe)
    (hsm : WardSmul) (hadd : WardYHAdd) (hmeas : WardHMeas) (hbd : WardHBoundL)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hbg : WardBgBoundL ε⁻¹ ν c U p M) :
    IsL2Family (bodyMeasure c γ ν) (wardHCoef c mZ ρb γ ν ε μ hχo χy U) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hold : ∀ T : StrG c mZ ρb γ ν, IsOldL2 c ν (strSum (chiOStr c mZ ρb γ ν hχo T)) :=
    fun T => wo_isOldL2_rep hcmp hρ hm hν hχo T
  obtain ⟨C, hC⟩ := hbd ν μ ε⁻¹ c γ M χy U p hχy hν hR hc hμ hbg
  obtain ⟨C', hC'⟩ := hcmp c mZ ρb γ ν hρ hm hν χo hχo
  refine ⟨fun T => ⟨hmeas ν μ ε⁻¹ c γ _ χy U p hχy hν hR hc hμ hUp _ (hold T), ?_⟩,
    fun T T' => ?_, fun r T => ?_, wo_bound_of hχo C C' (fun T => hC _ (hold T)) hC'⟩
  · exact lt_of_le_of_lt (hC _ (hold T))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hold T).memLp.2)
  · have h : wardHCoef c mZ ρb γ ν ε μ hχo χy U (T + T') =
        wardHCoef c mZ ρb γ ν ε μ hχo χy U T + wardHCoef c mZ ρb γ ν ε μ hχo χy U T' := by
      unfold wardHCoef
      rw [wo_wardH_congr hN hS hR hc χy U (wo_rep_add hρ hχo T T'), ← wo_coefOf_add]
      exact wo_coefOf_congr_offAxis hR.ne' fun τ y hy =>
        (hadd ν μ ε⁻¹ c χy U hχy hν hR hc hμ _ _ (hold T) (hold T') τ y hy).2
    rw [h]
  · have h : wardHCoef c mZ ρb γ ν ε μ hχo χy U (r • T) =
        r • wardHCoef c mZ ρb γ ν ε μ hχo χy U T := by
      unfold wardHCoef
      rw [wo_wardH_congr hN hS hR hc χy U (wo_rep_smul hρ hχo r T),
        (hsm ν μ ε⁻¹ c χy U 0 r _).2.1, wo_coefOf_smul]
    rw [h]

/-- **`Ẽ_μ[T]` is an `L²` family** in the ungained body measure (source 4271-4280, 4291-4294),
for a background with `WardBgBoundL`. -/
theorem wo_isL2Family_EL {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {M : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe)
    (hsm : WardSmul) (hadd : WardEAdd) (hmeas : WardEMeas) (hbd : WardEBoundL)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hbg : WardBgBoundL ε⁻¹ ν c U p M) :
    IsL2Family (srcMeasure c) (wardECoef c mZ ρb γ ν ε μ hχo χy U p) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hold : ∀ T : StrG c mZ ρb γ ν, IsOldL2 c ν (strSum (chiOStr c mZ ρb γ ν hχo T)) :=
    fun T => wo_isOldL2_rep hcmp hρ hm hν hχo T
  obtain ⟨C, hC⟩ := hbd ν μ ε⁻¹ c M χy U p hχy hν hR hc hμ hbg
  obtain ⟨C', hC'⟩ := hcmp c mZ ρb γ ν hρ hm hν χo hχo
  refine ⟨fun T => ⟨hmeas ν μ ε⁻¹ c _ χy U p hχy hν hR hc hμ hUp _ (hold T), ?_⟩,
    fun T T' => ?_, fun r T => ?_, wo_bound_of hχo C C' (fun T => hC _ (hold T)) hC'⟩
  · exact lt_of_le_of_lt (hC _ (hold T))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hold T).memLp.2)
  · have h : wardECoef c mZ ρb γ ν ε μ hχo χy U p (T + T') =
        wardECoef c mZ ρb γ ν ε μ hχo χy U p T + wardECoef c mZ ρb γ ν ε μ hχo χy U p T' := by
      unfold wardECoef
      rw [wo_wardE_congr hN hS hR hc χy U p (wo_rep_add hρ hχo T T'), ← wo_coefOf_add]
      exact wo_coefOf_congr_offAxis hR.ne' fun τ y hy =>
        hadd ν μ ε⁻¹ c χy U p hχy hν hR hc hμ _ _ (hold T) (hold T') τ y hy
    rw [h]
  · have h : wardECoef c mZ ρb γ ν ε μ hχo χy U p (r • T) =
        r • wardECoef c mZ ρb γ ν ε μ hχo χy U p T := by
      unfold wardECoef
      rw [wo_wardE_congr hN hS hR hc χy U p (wo_rep_smul hρ hχo r T),
        (hsm ν μ ε⁻¹ c χy U p r _).2.2, wo_coefOf_smul]
    rw [h]

end Families

/-- **The Ward fields exist as bounded linear maps at one regime** (source 4161-4303), for a
background with `WardBgBoundL`. -/
theorem wardTriple_exists_ofL {c mZ ρb γ ν ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    {χy : ℝ → ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {M : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe) (hsm : WardSmul)
    (hYH : WardYHAdd) (hEa : WardEAdd) (hYm : WardYMeas) (hHm : WardHMeas) (hEm : WardEMeas)
    (hYb : WardYBound) (hHb : WardHBoundL) (hEb : WardEBoundL)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hbg : WardBgBoundL ε⁻¹ ν c U p M) :
    ∃ t : (StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) × (StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) ×
        (StrG c mZ ρb γ ν →L[ℝ] SrcG c),
      IsWardTriple t.1 t.2.1 t.2.2 ε μ hχo χy U p := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have fY := wo_isL2Family_Y (γ := γ) hχo hN hS hcmp hsm hYH hYm hYb hχy hc hρ hm hν hε hμ
  have fH := wo_isL2Family_HL (γ := γ) hχo hN hS hcmp hsm hYH hHm hHb hχy hc hρ hm hν hε hμ hUp
    hbg
  have fE := wo_isL2Family_EL (γ := γ) hχo hN hS hcmp hsm hEa hEm hEb hχy hc hρ hm hν hε hμ hUp
    hbg
  refine ⟨(fY.toCLM, fH.toCLM, fE.toCLM), ?_⟩
  intro T g₁ g₂ h1 h2
  have hrep := wo_rep_ae hρ hχo T h1 h2
  refine ⟨(fY.toCLM_ae T).trans ?_, (fH.toCLM_ae T).trans ?_, (fE.toCLM_ae T).trans ?_⟩
  · show wardYCoef c mZ ρb γ ν ε μ hχo χy T =ᵐ[bodyMeasure c γ ν]
      coefOf ε⁻¹ (wardY ν μ ε⁻¹ c χy (g₁ + g₂))
    rw [wo_wardY_congr hN hS hR hc χy hrep]
    rfl
  · show wardHCoef c mZ ρb γ ν ε μ hχo χy U T =ᵐ[bodyMeasure c γ ν]
      coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U (g₁ + g₂))
    rw [wo_wardH_congr hN hS hR hc χy U hrep]
    rfl
  · show wardECoef c mZ ρb γ ν ε μ hχo χy U p T =ᵐ[srcMeasure c]
      coefOf ε⁻¹ (wardE ν μ ε⁻¹ c χy U p (g₁ + g₂))
    rw [wo_wardE_congr hN hS hR hc χy U p hrep]
    rfl

/-! ## 2. The background bound at actual levels -/

/-- **`WardBgBoundL` at actual levels** (source 2505-2562, 2607-2612, 2641-2642, 2706-2711,
5245-5260; 5926-5950): if the levels are actual for large `n` (with the ball datum
`IsActualLevel.ball`: the split of level `n` is the contraction-ball background of radius
`ρ_b = C₀ν_n^{-k₀}e^{m₀/ν_n}ε_n^{3/11}`), `D.Pl.mode` is the growing eigenvector and the ball
constants satisfy `m₀ > 0`, `2m₀ < 3d₋/11` (the contraction condition, 2510-2512) and `C₀ > 0`,
then for large `n` the level's background satisfies `WardBgBoundL` at `R = ε_n⁻¹`, `ν = ν_n`,
`c = c_n`, from `BgYoungW2` (at the exact split `IsActualLevel.split`), `BgPresY2B`
(instantiated at `Σ = D.Sig`, `m = m₀`, `C₁ = C₀`, `k₁ = k₀`, at the ball datum) and `ν_n → 0`. -/
theorem seq_wardBgBoundL (D : SeqData) {dm dp : ℝ} (hY : BgYoungW2) (hP : BgPresY2B)
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11)
    (hC0 : 0 < D.K.C0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∃ M : ℝ,
      WardBgBoundL (D.level n).ε⁻¹ (D.level n).ν (cOf (D.level n).ν) (D.level n).U
        (D.level n).pres M := by
  obtain ⟨n₀, hn₀⟩ := hact.exists
  have hdm : 0 < dm := hn₀.regime.dm_pos
  obtain ⟨ν₁, hν₁, H1⟩ := hY _ _ hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := hP D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos hq D.K.m0 hm0 dm dp hdm
    h2m D.K.C0 D.K.k0 hC0
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < min ν₁ ν₂ :=
    (tendsto_order.1 (retNu_tendsto D.σ₀ hω)).2 _ (lt_min hν₁ hν₂)
  filter_upwards [hact, hsmall] with n hn hlt
  have hle1 : ((D.level n).params D.Pl).ν ≤ ν₁ := (hlt.trans_le (min_le_left _ _)).le
  have hle2 : ((D.level n).params D.Pl).ν ≤ ν₂ := (hlt.trans_le (min_le_right _ _)).le
  obtain ⟨M₁, hM₁⟩ := H1 ((D.level n).params D.Pl) _ _ _ (D.V n) (D.rb n) (D.pres n) hn.regime
    hle1 rfl hn.split hn.profile
  exact wardBgBoundL_of_level hM₁
    (H2 ((D.level n).params D.Pl) _ hn.regime hle2 rfl rfl (D.V n) (D.rb n) (D.pres n) hn.ball
      hn.profile)

/-! ## 3. Along the sequence -/

/-- **The Ward fields along the sequence at actual levels** (source 4161-4303, 5926-5950): for
large `n` and every `z ∈ [-1, 1]`, at `μ = μ_n(z)`, there is a triple of bounded linear maps with
`IsWardTriple` on the level's background `U = V + r_b` and pressure, from the leaves, the actual
levels (with their ball datum), the growing eigenpair, the ball constants (`m₀ > 0`,
`2m₀ < 3d₋/11`, `C₀ > 0`; source 2505-2524, 2706-2711) and the background facts `BgYoungW2`,
`BgPresY2B`; no background hypothesis remains. -/
theorem seqWardTriple_exists_ofL (D : SeqData) {dm dp : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe) (hsm : WardSmul)
    (hYH : WardYHAdd) (hEa : WardEAdd) (hYm : WardYMeas) (hHm : WardHMeas) (hEm : WardEMeas)
    (hYb : WardYBound) (hHb : WardHBoundL) (hEb : WardEBoundL) (hY : BgYoungW2) (hP : BgPresY2B)
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hm0 : 0 < D.K.m0)
    (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (hmZ : 0 ≤ D.K.mZ) (hχy : IsYoungCutoff D.K.χy)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U
          (D.level n).pres := by
  filter_upwards [hact, seq_wardBgBoundL D hY hP hq hω hm0 h2m hC0 hact,
    mu_eventually_mem D hω hσ0 hσ1] with n hn hb hmu z hz
  obtain ⟨M, hM⟩ := hb
  have hμ : -(1 / 4) < D.mu n z := by
    have h1 := (hmu z hz).1
    linarith
  exact wardTriple_exists_ofL D.K.hχo hN hS hcmp hsm hYH hEa hYm hHm hEm hYb hHb hEb hχy
    (cOf_pos (D.level n).ν_pos) (wo_rhoB_pos D.Pl D.K (D.level n) hC0) hmZ (D.level n).ν_pos
    (D.level n).ε_pos hμ hn.profile hM

end UnforcedLeray.Short.PartIIIb.Concrete
