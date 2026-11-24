import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# The Ward fields exist as bounded linear maps: assembly (source 4161-4303)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `ORG:return-concrete/instance-3/ward`.  From the leaves of `Ward/Defs.lean`:

* `wo_isL2Family_Y`, `wo_isL2Family_H`, `wo_isL2Family_E`: the coefficient families
  `T ↦ wardYCoef T`, `wardHCoef T` (gained body measure) and `wardECoef T` (ungained body
  measure) are `IsL2Family`s: `L²` (measurability leaves and the bounds), linear a.e. (the
  canonical old source is linear a.e., `wo_rep_add`/`wo_rep_smul`; the fields depend only on its
  a.e. class, `wo_wardY_congr`…; they are additive off the axis, `WardYHAdd`/`WardEAdd`, and
  homogeneous, `WardSmul`; `coefOf` reads them only off the axis), and bounded (the bound leaves and
  `WardOldNormLe`);
* `wardTriple_exists_of`: at one regime the three `toCLM`s satisfy `IsWardTriple`, for every
  choice of the representatives `g₁, g₂` (`wo_rep_ae`, `wo_wardY_congr`…);
* `seqWardTriple_exists_of`: along the sequence, for large `n` and `z ∈ [-1, 1]`, at
  `μ = D.mu n z` (`mu_eventually_mem`: `μ ∈ [σ₀/2, (σ₀ + 1/4)/2]`), from the actual levels
  (`SeqData.IsActualLevel`: the exact profile, 4139-4141) and the background bounds on the young
  support (`WardBgBound`, source 4155, 4194-4195, 4291-4294).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The three coefficient families are `L²` families -/

section Families

variable {c mZ ρb γ ν ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {χy : ℝ → ℝ}

include hχo in
/-- A bound of a family in the old data and `WardOldNormLe` give the bound of `IsL2Family`. -/
theorem wo_bound_of {m : Measure Chart} {F : StrG c mZ ρb γ ν → Chart → Merid} (C C' : ℝ)
    (hF : ∀ T, eLpNorm (F T) 2 m ≤
      ENNReal.ofReal C * eLpNorm (strSum (chiOStr c mZ ρb γ ν hχo T)) 2 (ageμ c (-1 / 2)))
    (hC' : ∀ T, eLpNorm (strSum (chiOStr c mZ ρb γ ν hχo T)) 2 (ageμ c (-1 / 2)) ≤
      ENNReal.ofReal (C' * ‖T‖)) :
    ∃ K : ℝ, ∀ T, eLpNorm (F T) 2 m ≤ ENNReal.ofReal (K * ‖T‖) := by
  refine ⟨max C 0 * C', fun T => ?_⟩
  calc eLpNorm (F T) 2 m
      ≤ ENNReal.ofReal C * eLpNorm (strSum (chiOStr c mZ ρb γ ν hχo T)) 2 (ageμ c (-1 / 2)) :=
        hF T
    _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (C' * ‖T‖) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (hC' T)
    _ = ENNReal.ofReal (max C 0 * C' * ‖T‖) := by
        rw [mul_assoc, ENNReal.ofReal_mul (le_max_right _ _)]

/-- **`Y[T]` is an `L²` family** in the gained body measure (source 4171-4174, 4194-4196). -/
theorem wo_isL2Family_Y (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe)
    (hsm : WardSmul) (hadd : WardYHAdd) (hmeas : WardYMeas) (hbd : WardYBound)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) :
    IsL2Family (bodyMeasure c γ ν) (wardYCoef c mZ ρb γ ν ε μ hχo χy) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hold : ∀ T : StrG c mZ ρb γ ν, IsOldL2 c ν (strSum (chiOStr c mZ ρb γ ν hχo T)) :=
    fun T => wo_isOldL2_rep hcmp hρ hm hν hχo T
  obtain ⟨C, hC⟩ := hbd ν μ ε⁻¹ c γ χy hχy hν hR hc hμ
  obtain ⟨C', hC'⟩ := hcmp c mZ ρb γ ν hρ hm hν χo hχo
  refine ⟨fun T => ⟨hmeas ν μ ε⁻¹ c γ χy hχy hν hR hc hμ _ (hold T), ?_⟩, fun T T' => ?_,
    fun r T => ?_, wo_bound_of hχo C C' (fun T => hC _ (hold T)) hC'⟩
  · exact lt_of_le_of_lt (hC _ (hold T))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hold T).memLp.2)
  · have h : wardYCoef c mZ ρb γ ν ε μ hχo χy (T + T') =
        wardYCoef c mZ ρb γ ν ε μ hχo χy T + wardYCoef c mZ ρb γ ν ε μ hχo χy T' := by
      unfold wardYCoef
      rw [wo_wardY_congr hN hS hR hc χy (wo_rep_add hρ hχo T T'), ← wo_coefOf_add]
      exact wo_coefOf_congr_offAxis hR.ne' fun τ y hy =>
        (hadd ν μ ε⁻¹ c χy 0 hχy hν hR hc hμ _ _ (hold T) (hold T') τ y hy).1
    rw [h]
  · have h : wardYCoef c mZ ρb γ ν ε μ hχo χy (r • T) =
        r • wardYCoef c mZ ρb γ ν ε μ hχo χy T := by
      unfold wardYCoef
      rw [wo_wardY_congr hN hS hR hc χy (wo_rep_smul hρ hχo r T), (hsm ν μ ε⁻¹ c χy 0 0 r _).1,
        wo_coefOf_smul]
    rw [h]

/-- **`h[T]` is an `L²` family** in the gained body measure (source 4171-4174, 4194-4195). -/
theorem wo_isL2Family_H {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {M : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe)
    (hsm : WardSmul) (hadd : WardYHAdd) (hmeas : WardHMeas) (hbd : WardHBound)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hbg : WardBgBound ε⁻¹ ν U p M) :
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

/-- **`Ẽ_μ[T]` is an `L²` family** in the ungained body measure (source 4271-4280, 4291-4294). -/
theorem wo_isL2Family_E {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {M : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe)
    (hsm : WardSmul) (hadd : WardEAdd) (hmeas : WardEMeas) (hbd : WardEBound)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hbg : WardBgBound ε⁻¹ ν U p M) :
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

/-! ## 2. The Ward triple at one regime -/

/-- **The Ward fields exist as bounded linear maps at one regime** (source 4161-4303): from the
leaves, the `toCLM`s of the three coefficient families satisfy `IsWardTriple` (for every choice of
the representatives `g₁, g₂` of the components of `χ_oT`). -/
theorem wardTriple_exists_of {c mZ ρb γ ν ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    {χy : ℝ → ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} {M : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe) (hsm : WardSmul)
    (hYH : WardYHAdd) (hEa : WardEAdd) (hYm : WardYMeas) (hHm : WardHMeas) (hEm : WardEMeas)
    (hYb : WardYBound) (hHb : WardHBound) (hEb : WardEBound)
    (hχy : IsYoungCutoff χy) (hc : 0 < c) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hbg : WardBgBound ε⁻¹ ν U p M) :
    ∃ t : (StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) × (StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) ×
        (StrG c mZ ρb γ ν →L[ℝ] SrcG c),
      IsWardTriple t.1 t.2.1 t.2.2 ε μ hχo χy U p := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have fY := wo_isL2Family_Y (γ := γ) hχo hN hS hcmp hsm hYH hYm hYb hχy hc hρ hm hν hε hμ
  have fH := wo_isL2Family_H (γ := γ) hχo hN hS hcmp hsm hYH hHm hHb hχy hc hρ hm hν hε hμ hUp
    hbg
  have fE := wo_isL2Family_E (γ := γ) hχo hN hS hcmp hsm hEa hEm hEb hχy hc hρ hm hν hε hμ hUp
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

/-! ## 3. Along the sequence (source 5926-5950) -/

/-- The repair bound `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` of a level is positive when `C₀ > 0`
(source 2703-2713). -/
theorem wo_rhoB_pos (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) :
    0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  have hν : 0 < (L.params Pl).ν := L.ν_pos
  have hε : 0 < (L.params Pl).ε := L.ε_pos
  exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos hν _))) (Real.exp_pos _))
    (Real.rpow_pos_of_pos hε _)

/-- **The Ward fields along the sequence at actual levels** (source 4161-4303, 5926-5950): for
large `n` and every `z ∈ [-1, 1]`, at `μ = μ_n(z)`, there is a triple of bounded linear maps with
`IsWardTriple` on the level's background `U = V + r_b` and pressure, from the leaves, the actual
levels (the exact profile) and the background bounds on the young support. -/
theorem seqWardTriple_exists_of (D : SeqData) {dm dp : ℝ}
    (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hcmp : WardOldNormLe) (hsm : WardSmul)
    (hYH : WardYHAdd) (hEa : WardEAdd) (hYm : WardYMeas) (hHm : WardHMeas) (hEm : WardEMeas)
    (hYb : WardYBound) (hHb : WardHBound) (hEb : WardEBound)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hC0 : 0 < D.K.C0)
    (hmZ : 0 ≤ D.K.mZ) (hχy : IsYoungCutoff D.K.χy)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n)
    (hbg : ∀ᶠ n : ℕ in atTop, ∃ M : ℝ,
      WardBgBound (D.level n).ε⁻¹ (D.level n).ν (D.level n).U (D.level n).pres M) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U
          (D.level n).pres := by
  filter_upwards [hact, hbg, mu_eventually_mem D hω hσ0 hσ1] with n hn hb hmu z hz
  obtain ⟨M, hM⟩ := hb
  have hμ : -(1 / 4) < D.mu n z := by
    have h1 := (hmu z hz).1
    linarith
  exact wardTriple_exists_of D.K.hχo hN hS hcmp hsm hYH hEa hYm hHm hEm hYb hHb hEb hχy
    (cOf_pos (D.level n).ν_pos) (wo_rhoB_pos D.Pl D.K (D.level n) hC0) hmZ (D.level n).ν_pos
    (D.level n).ε_pos hμ hn.profile hM

end UnforcedLeray.Short.PartIIIb.Concrete
